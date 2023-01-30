Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGrotate.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__crossbar2.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoffunique.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray2.
Require Export lemma__ray4.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__sameside2.
Require Export lemma__samesidecollinear.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplementinequality.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__07.
Require Export proposition__23C.
Require Export proposition__31.
Require Export proposition__34.
Require Export proposition__38.
Require Export proposition__41.
Definition proposition__42 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (J: euclidean__axioms.Point) (K: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.nCol J D K) -> ((euclidean__defs.Midpoint B E C) -> (exists (X: euclidean__axioms.Point) (Z: euclidean__axioms.Point), (euclidean__defs.PG X E C Z) /\ ((euclidean__axioms.EF A B E C X E C Z) /\ ((euclidean__defs.CongA C E X J D K) /\ (euclidean__axioms.Col X Z A)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro J.
intro K.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H2.
- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H2.
-- exact H1.
-- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as __TmpHyp.
--- exact H2.
--- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H3.
---- exact __TmpHyp.
---- destruct H3 as [H3 H4].
split.
----- exact H3.
----- exact H4.
- assert (* Cut *) (euclidean__axioms.Cong E B E C) as H3.
-- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* Cut *) ((euclidean__axioms.Cong E B C E) /\ ((euclidean__axioms.Cong E B E C) /\ (euclidean__axioms.Cong B E C E))) as H5.
---- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (E) (E) (C) H4).
---- assert (* AndElim *) ((euclidean__axioms.Cong E B C E) /\ ((euclidean__axioms.Cong E B E C) /\ (euclidean__axioms.Cong B E C E))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Cong E B E C) /\ (euclidean__axioms.Cong B E C E)) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
exact H8.
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
--- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H4.
---- exact H2.
---- destruct H4 as [H4 H5].
exact H.
--- assert (* Cut *) (euclidean__axioms.Col B E C) as H5.
---- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H5.
----- exact H2.
----- destruct H5 as [H5 H6].
right.
right.
right.
right.
left.
exact H5.
---- assert (* Cut *) (euclidean__axioms.nCol B C A) as H6.
----- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H6.
------ exact H2.
------ destruct H6 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H8.
------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H4).
------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H11.
----- assert (* Cut *) (euclidean__axioms.Col B C E) as H7.
------ assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H7.
------- exact H2.
------- destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H9.
-------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (C) H5).
-------- assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
exact H16.
------ assert (* Cut *) (C = C) as H8.
------- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H8.
-------- exact H2.
-------- destruct H8 as [H8 H9].
apply (@logic.eq__refl (Point) C).
------- assert (* Cut *) (euclidean__axioms.Col B C C) as H9.
-------- right.
right.
left.
exact H8.
-------- assert (* Cut *) (euclidean__axioms.neq E C) as H10.
--------- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H10.
---------- exact H2.
---------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H12.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (C) H10).
----------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C)) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
exact H13.
--------- assert (* Cut *) (euclidean__axioms.nCol E C A) as H11.
---------- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H11.
----------- exact H2.
----------- destruct H11 as [H11 H12].
apply (@euclidean__tactics.nCol__notCol (E) (C) (A)).
------------apply (@euclidean__tactics.nCol__not__Col (E) (C) (A)).
-------------apply (@lemma__NChelper.lemma__NChelper (B) (C) (A) (E) (C) (H6) (H7) (H9) H10).


---------- assert (* Cut *) (exists (f: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.Out E C c) /\ ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C))) as H12.
----------- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H12.
------------ exact H2.
------------ destruct H12 as [H12 H13].
apply (@proposition__23C.proposition__23C (E) (C) (D) (J) (K) (A) (H10) (H0) H11).
----------- assert (exists f: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point), (euclidean__defs.Out E C c) /\ ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C)))) as H13.
------------ exact H12.
------------ destruct H13 as [f H13].
assert (exists c: euclidean__axioms.Point, ((euclidean__defs.Out E C c) /\ ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C)))) as H14.
------------- exact H13.
------------- destruct H14 as [c H14].
assert (* AndElim *) ((euclidean__defs.Out E C c) /\ ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H19.
---------------- exact H2.
---------------- destruct H19 as [H19 H20].
assert (* Cut *) (euclidean__axioms.nCol B C A) as H21.
----------------- assert (* Cut *) ((euclidean__axioms.nCol C E A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E))))) as H21.
------------------ apply (@lemma__NCorder.lemma__NCorder (E) (C) (A) H11).
------------------ assert (* AndElim *) ((euclidean__axioms.nCol C E A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E))))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E)))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E)) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
exact H6.
----------------- assert (* Cut *) (exists (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))))))))) as H22.
------------------ apply (@proposition__31.proposition__31 (A) (B) (C) (E) (H19) H21).
------------------ assert (exists P: euclidean__axioms.Point, (exists (Q: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))))))))) as H23.
------------------- exact H22.
------------------- destruct H23 as [P H23].
assert (exists Q: euclidean__axioms.Point, (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))))))))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [Q H24].
assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))))))))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [M H25].
assert (* AndElim *) ((euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))))))))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))))))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))))))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))))) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))))) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))) as H46.
-------------------------------- exact H45.
-------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))))) as H48.
--------------------------------- exact H47.
--------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))) as H50.
---------------------------------- exact H49.
---------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E))) as H52.
----------------------------------- exact H51.
----------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)) as H54.
------------------------------------ exact H53.
------------------------------------ destruct H54 as [H54 H55].
assert (* Cut *) (euclidean__defs.CongA A E C P A E) as H56.
------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (A) (E) (A) (E) (C) H34).
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P A E) as H57.
-------------------------------------- apply (@euclidean__tactics.nCol__notCol (P) (A) (E)).
---------------------------------------apply (@euclidean__tactics.nCol__not__Col (P) (A) (E)).
----------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (E) (C) (P) (A) (E) H56).


-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A P) as H58.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol E P A) /\ ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P))))) as H58.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder (P) (A) (E) H57).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol E P A) /\ ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P))))) as H59.
----------------------------------------- exact H58.
----------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol E P A) /\ ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P)))) as H61.
------------------------------------------ exact H60.
------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol E P A) /\ ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P))) as H63.
------------------------------------------- exact H62.
------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P)) as H65.
-------------------------------------------- exact H64.
-------------------------------------------- destruct H65 as [H65 H66].
exact H66.
--------------------------------------- assert (* Cut *) (euclidean__defs.OS A f E C) as H59.
---------------------------------------- assert (* Cut *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H59.
----------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (C) (f) (A) H18).
----------------------------------------- assert (* AndElim *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H60.
------------------------------------------ exact H59.
------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E)) as H62.
------------------------------------------- exact H61.
------------------------------------------- destruct H62 as [H62 H63].
exact H60.
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H60.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol P E A) /\ ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E))))) as H60.
------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (E) (A) (P) H58).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol P E A) /\ ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E))))) as H61.
------------------------------------------- exact H60.
------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol P E A) /\ ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E)))) as H63.
-------------------------------------------- exact H62.
-------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.nCol P E A) /\ ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E))) as H65.
--------------------------------------------- exact H64.
--------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E)) as H67.
---------------------------------------------- exact H66.
---------------------------------------------- destruct H67 as [H67 H68].
exact H21.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H61.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col C C B) /\ ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B))))) as H61.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (C) H9).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col C C B) /\ ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B))))) as H62.
-------------------------------------------- exact H61.
-------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col C C B) /\ ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B)))) as H64.
--------------------------------------------- exact H63.
--------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B))) as H66.
---------------------------------------------- exact H65.
---------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B)) as H68.
----------------------------------------------- exact H67.
----------------------------------------------- destruct H68 as [H68 H69].
exact H7.
------------------------------------------ assert (* Cut *) (B = B) as H62.
------------------------------------------- apply (@logic.eq__refl (Point) B).
------------------------------------------- assert (* Cut *) (A = A) as H63.
-------------------------------------------- apply (@logic.eq__refl (Point) A).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H64.
--------------------------------------------- right.
left.
exact H62.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H65.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H65.
----------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (C) H19).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H66.
------------------------------------------------ exact H65.
------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C)) as H68.
------------------------------------------------- exact H67.
------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E A) as H66.
----------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (E) (A)).
------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (E) (A)).
-------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (B) (C) (A) (B) (E) (H60) (H64) (H61) H65).


----------------------------------------------- assert (* Cut *) (C = C) as H67.
------------------------------------------------ exact H8.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C C) as H68.
------------------------------------------------- exact H9.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H69.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H69.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (E) H55).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H70.
---------------------------------------------------- exact H69.
---------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E)) as H72.
----------------------------------------------------- exact H71.
----------------------------------------------------- destruct H72 as [H72 H73].
exact H10.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H70.
--------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (C) H69).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H71.
---------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (E) (A)).
-----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (E) (A)).
------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (B) (C) (A) (C) (E) (H60) (H68) (H61) H70).


---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H72.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)))))) as H72.
------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (C) (E) (A) H71).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)))))) as H73.
------------------------------------------------------- exact H72.
------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))))) as H75.
-------------------------------------------------------- exact H74.
-------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)))) as H77.
--------------------------------------------------------- exact H76.
--------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H79.
---------------------------------------------------------- exact H78.
---------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)) as H81.
----------------------------------------------------------- exact H80.
----------------------------------------------------------- destruct H81 as [H81 H82].
exact H75.
----------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Meet E f P Q))) as H73.
------------------------------------------------------ intro H73.
assert (* Cut *) (~(euclidean__defs.LtA C E f C E A)) as H74.
------------------------------------------------------- intro H74.
assert (* Cut *) (euclidean__defs.Out E C C) as H75.
-------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (C) (C)).
---------------------------------------------------------right.
left.
exact H67.

--------------------------------------------------------- exact H69.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E A A) as H76.
--------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (A) (A)).
----------------------------------------------------------right.
left.
exact H63.

---------------------------------------------------------- exact H72.
--------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m C) /\ (euclidean__defs.Out E f m)) as H77.
---------------------------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (f) (E) (C) (A) (C) (A) (H74) (H18) (H75) H76).
---------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m C) /\ (euclidean__defs.Out E f m))) as H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- destruct H78 as [m H78].
assert (* AndElim *) ((euclidean__axioms.BetS A m C) /\ (euclidean__defs.Out E f m)) as H79.
------------------------------------------------------------ exact H78.
------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* Cut *) (euclidean__axioms.BetS C m A) as H81.
------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (C) H79).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C M P) as H82.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (M) (C) H52).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E M A) as H83.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (E) H55).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M E A M) as H84.
---------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (A) (M) (E) H46).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E M A M) as H85.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H85.
------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (M) (E) (A) (M) H84).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H86.
------------------------------------------------------------------- exact H85.
------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A)) as H88.
-------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------- destruct H88 as [H88 H89].
exact H88.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C P M) as H86.
------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (P) (M) (C) H48).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong M C M P) as H87.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M M P) /\ ((euclidean__axioms.Cong C M P M) /\ (euclidean__axioms.Cong M C M P))) as H87.
-------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (C) (P) (M) H86).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C M M P) /\ ((euclidean__axioms.Cong C M P M) /\ (euclidean__axioms.Cong M C M P))) as H88.
--------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Cong C M P M) /\ (euclidean__axioms.Cong M C M P)) as H90.
---------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H91.
------------------------------------------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS P A F)) as H88.
-------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Euclid5 (m) (E) (A) (C) (P) (M) (H82) (H83) (H81) (H85) (H87) H58).
-------------------------------------------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS P A F))) as H89.
--------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------- destruct H89 as [F H89].
assert (* AndElim *) ((euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS P A F)) as H90.
---------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* Cut *) (euclidean__axioms.Col E m F) as H92.
----------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H90.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E F) as H93.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H93.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (m) (F) H92).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H94.
-------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)))) as H96.
--------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))) as H98.
---------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)) as H100.
----------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H94.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E f m) as H94.
------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (E) (f) (m) H80).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E f) as H95.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H95.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (f) (m) H94).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H96.
---------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E)))) as H98.
----------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))) as H100.
------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E)) as H102.
------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H100.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H96.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H96.
---------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (m) (F) H90).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H97.
----------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F)) as H99.
------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------ destruct H99 as [H99 H100].
exact H99.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m E) as H97.
---------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (m) H96).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f F) as H98.
----------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (f) (F)).
------------------------------------------------------------------------------intro H98.
apply (@euclidean__tactics.Col__nCol__False (E) (f) (F) (H98)).
-------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (m) (E) (f) (F) (H95) (H93) H97).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A F) as H99.
------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H91.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P A Q) as H100.
------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H26.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H101.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P F))) as H101.
--------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (F) H91).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P F))) as H102.
---------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P F)) as H104.
----------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H104.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A P) as H102.
--------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (A) H101).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A P F) as H103.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H103.
----------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (F) H99).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H104.
------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P)))) as H106.
------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))) as H108.
-------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P)) as H110.
--------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H104.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A P Q) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (Q) H100).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P)))) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))) as H109.
--------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P)) as H111.
---------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H105.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P F Q) as H105.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (P) (F) (Q)).
-------------------------------------------------------------------------------------intro H105.
apply (@euclidean__tactics.Col__nCol__False (P) (F) (Q) (H105)).
--------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (P) (F) (Q) (H103) (H104) H102).


------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P Q F) as H106.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P))))) as H106.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (F) (Q) H105).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P))))) as H107.
--------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P)))) as H109.
---------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P))) as H111.
----------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P)) as H113.
------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
exact H113.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H107.
-------------------------------------------------------------------------------------- apply (@lemma__ray2.lemma__ray2 (E) (f) (m) H80).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H108.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H108.
---------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (Q) H26).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H109.
----------------------------------------------------------------------------------------- exact H108.
----------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q)) as H111.
------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------ destruct H111 as [H111 H112].
exact H112.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H109.
---------------------------------------------------------------------------------------- exists F.
split.
----------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------- apply (@H73 H109).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C B) as H75.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H75.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H61).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H76.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H80.
------------------------------------------------------------ exact H79.
------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H82.
------------------------------------------------------------- exact H81.
------------------------------------------------------------- destruct H82 as [H82 H83].
exact H83.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H76.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H76.
---------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (E) H55).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H77.
----------------------------------------------------------- exact H76.
----------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E)) as H79.
------------------------------------------------------------ exact H78.
------------------------------------------------------------ destruct H79 as [H79 H80].
exact H65.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H77.
---------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H76).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A f E B) as H78.
----------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (E) (C) (B) (A) (f) (H59) (H75) H77).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS f A E B) as H79.
------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.OS f A E B) /\ ((euclidean__defs.OS A f B E) /\ (euclidean__defs.OS f A B E))) as H79.
------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (B) (A) (f) H78).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS f A E B) /\ ((euclidean__defs.OS A f B E) /\ (euclidean__defs.OS f A B E))) as H80.
-------------------------------------------------------------- exact H79.
-------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__defs.OS A f B E) /\ (euclidean__defs.OS f A B E)) as H82.
--------------------------------------------------------------- exact H81.
--------------------------------------------------------------- destruct H82 as [H82 H83].
exact H80.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS C E B) as H80.
------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (E) (C) H19).
------------------------------------------------------------- assert (* Cut *) (A = A) as H81.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- assert (* Cut *) (f = f) as H82.
--------------------------------------------------------------- apply (@logic.eq__refl (Point) f).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B f) as H83.
---------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))))) as H83.
----------------------------------------------------------------- exact H79.
----------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))))) as __TmpHyp.
------------------------------------------------------------------ exact H83.
------------------------------------------------------------------ assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A))))))) as H84.
------------------------------------------------------------------- exact __TmpHyp.
------------------------------------------------------------------- destruct H84 as [x H84].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U x) /\ ((euclidean__axioms.BetS A V x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A))))))) as H85.
-------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------- destruct H85 as [x0 H85].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f x0 x) /\ ((euclidean__axioms.BetS A V x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A))))))) as H86.
--------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------- destruct H86 as [x1 H86].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.Col E B x1) /\ ((euclidean__axioms.BetS f x0 x) /\ ((euclidean__axioms.BetS A x1 x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))))) as H87.
---------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col E B x1) /\ ((euclidean__axioms.BetS f x0 x) /\ ((euclidean__axioms.BetS A x1 x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A))))) as H89.
----------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.BetS f x0 x) /\ ((euclidean__axioms.BetS A x1 x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))) as H91.
------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.BetS A x1 x) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A))) as H93.
------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)) as H95.
-------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))))) as H97.
--------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))))) as __TmpHyp0.
---------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f))))))) as H98.
----------------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------------- destruct H98 as [x2 H98].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U x2) /\ ((euclidean__axioms.BetS f V x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f))))))) as H99.
------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------ destruct H99 as [x3 H99].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col E B x3) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A x3 x2) /\ ((euclidean__axioms.BetS f V x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f))))))) as H100.
------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------- destruct H100 as [x4 H100].
assert (* AndElim *) ((euclidean__axioms.Col E B x3) /\ ((euclidean__axioms.Col E B x4) /\ ((euclidean__axioms.BetS A x3 x2) /\ ((euclidean__axioms.BetS f x4 x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))))) as H101.
-------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col E B x4) /\ ((euclidean__axioms.BetS A x3 x2) /\ ((euclidean__axioms.BetS f x4 x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f))))) as H103.
--------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.BetS A x3 x2) /\ ((euclidean__axioms.BetS f x4 x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))) as H105.
---------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.BetS f x4 x2) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f))) as H107.
----------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)) as H109.
------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))))) as H111.
------------------------------------------------------------------------------------- exact H59.
------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))))) as __TmpHyp1.
-------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f))))))) as H112.
--------------------------------------------------------------------------------------- exact __TmpHyp1.
--------------------------------------------------------------------------------------- destruct H112 as [x5 H112].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U x5) /\ ((euclidean__axioms.BetS f V x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f))))))) as H113.
---------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------- destruct H113 as [x6 H113].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col E C x6) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A x6 x5) /\ ((euclidean__axioms.BetS f V x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f))))))) as H114.
----------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------- destruct H114 as [x7 H114].
assert (* AndElim *) ((euclidean__axioms.Col E C x6) /\ ((euclidean__axioms.Col E C x7) /\ ((euclidean__axioms.BetS A x6 x5) /\ ((euclidean__axioms.BetS f x7 x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))))) as H115.
------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col E C x7) /\ ((euclidean__axioms.BetS A x6 x5) /\ ((euclidean__axioms.BetS f x7 x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f))))) as H117.
------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.BetS A x6 x5) /\ ((euclidean__axioms.BetS f x7 x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))) as H119.
-------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.BetS f x7 x5) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f))) as H121.
--------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)) as H123.
---------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))))) as H125.
----------------------------------------------------------------------------------------------- exact H18.
----------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------ assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A))))))) as H126.
------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------- destruct H126 as [x8 H126].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U x8) /\ ((euclidean__axioms.BetS A V x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A))))))) as H127.
-------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------- destruct H127 as [x9 H127].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col E C x9) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f x9 x8) /\ ((euclidean__axioms.BetS A V x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A))))))) as H128.
--------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------- destruct H128 as [x10 H128].
assert (* AndElim *) ((euclidean__axioms.Col E C x9) /\ ((euclidean__axioms.Col E C x10) /\ ((euclidean__axioms.BetS f x9 x8) /\ ((euclidean__axioms.BetS A x10 x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))))) as H129.
---------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col E C x10) /\ ((euclidean__axioms.BetS f x9 x8) /\ ((euclidean__axioms.BetS A x10 x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A))))) as H131.
----------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.BetS f x9 x8) /\ ((euclidean__axioms.BetS A x10 x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))) as H133.
------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------ destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.BetS A x10 x8) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A))) as H135.
------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)) as H137.
-------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H110.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H84.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq B f) /\ ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E)))))) as H84.
------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (E) (B) (f) H83).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq B f) /\ ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E)))))) as H85.
------------------------------------------------------------------- exact H84.
------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq B f) /\ ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E))))) as H87.
-------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E)))) as H89.
--------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E))) as H91.
---------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E)) as H93.
----------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------- destruct H93 as [H93 H94].
exact H89.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E C) as H85.
------------------------------------------------------------------ exact H5.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E B C) as H86.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H86.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (C) H85).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H87.
--------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)))) as H89.
---------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))) as H91.
----------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)) as H93.
------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------ destruct H93 as [H93 H94].
exact H87.
------------------------------------------------------------------- assert (* Cut *) (E = E) as H87.
-------------------------------------------------------------------- apply (@logic.eq__refl (Point) E).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B E) as H88.
--------------------------------------------------------------------- right.
left.
exact H87.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E C f) as H89.
---------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (C) (f)).
-----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (E) (C) (f)).
------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (E) (B) (f) (E) (C) (H83) (H88) (H86) H69).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E f) as H90.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C E f) /\ ((euclidean__axioms.nCol C f E) /\ ((euclidean__axioms.nCol f E C) /\ ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E))))) as H90.
------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (E) (C) (f) H89).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol C E f) /\ ((euclidean__axioms.nCol C f E) /\ ((euclidean__axioms.nCol f E C) /\ ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E))))) as H91.
------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.nCol C f E) /\ ((euclidean__axioms.nCol f E C) /\ ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E)))) as H93.
-------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.nCol f E C) /\ ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E))) as H95.
--------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E)) as H97.
---------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H91.
----------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA C E A C E f)) as H91.
------------------------------------------------------------------------ intro H91.
assert (* Cut *) (euclidean__defs.Out E A A) as H92.
------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (A) (A)).
--------------------------------------------------------------------------right.
left.
exact H81.

-------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E f f) as H93.
-------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (f) (f)).
---------------------------------------------------------------------------right.
left.
exact H82.

--------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp C E A A B) as H94.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp C E f f B) as H95.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA f E B A E B) as H96.
----------------------------------------------------------------------------- apply (@lemma__supplementinequality.lemma__supplementinequality (C) (E) (f) (f) (B) (C) (E) (A) (A) (B) (H95) (H94) H91).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E f) as H97.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B E f) /\ ((euclidean__axioms.nCol B f E) /\ ((euclidean__axioms.nCol f E B) /\ ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E))))) as H97.
------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (B) (f) H83).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B E f) /\ ((euclidean__axioms.nCol B f E) /\ ((euclidean__axioms.nCol f E B) /\ ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E))))) as H98.
-------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.nCol B f E) /\ ((euclidean__axioms.nCol f E B) /\ ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E)))) as H100.
--------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol f E B) /\ ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E))) as H102.
---------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E)) as H104.
----------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H98.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B E f f E B) as H98.
------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (E) (f) H97).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B E f A E B) as H99.
-------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (f) (E) (B) (A) (E) (B) (B) (E) (f) (H96) H98).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E A A E B) as H100.
--------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (E) (A) H66).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B E f B E A) as H101.
---------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (E) (f) (A) (E) (B) (B) (E) (A) (H99) H100).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E B B) as H102.
----------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (B) (B)).
------------------------------------------------------------------------------------right.
left.
exact H62.

------------------------------------------------------------------------------------ exact H77.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E A A) as H103.
------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------ assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m B) /\ (euclidean__defs.Out E f m)) as H104.
------------------------------------------------------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (f) (E) (B) (A) (B) (A) (H101) (H79) (H102) H103).
------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m B) /\ (euclidean__defs.Out E f m))) as H105.
-------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------- destruct H105 as [m H105].
assert (* AndElim *) ((euclidean__axioms.BetS A m B) /\ (euclidean__defs.Out E f m)) as H106.
--------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* Cut *) (euclidean__axioms.BetS B m A) as H108.
---------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (B) H106).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E M A) as H109.
----------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (E) H55).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M E A M) as H110.
------------------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (A) (M) (E) H46).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E M A M) as H111.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H111.
-------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (E) (A) (M) H110).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H112.
--------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A)) as H114.
---------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
exact H114.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M B M Q) as H112.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H112.
--------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (M) (M) (Q) H50).
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H113.
---------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M)) as H115.
----------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
exact H115.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P A E) as H113.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B f) /\ ((euclidean__axioms.nCol E f B) /\ ((euclidean__axioms.nCol f B E) /\ ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B))))) as H113.
---------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (E) (f) H97).
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B f) /\ ((euclidean__axioms.nCol E f B) /\ ((euclidean__axioms.nCol f B E) /\ ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B))))) as H114.
----------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.nCol E f B) /\ ((euclidean__axioms.nCol f B E) /\ ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B)))) as H116.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.nCol f B E) /\ ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B))) as H118.
------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B)) as H120.
-------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H57.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A Q) as H114.
---------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H26.
---------------------------------------------------------------------------------------------- assert (* Cut *) (A = A) as H115.
----------------------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A A) as H116.
------------------------------------------------------------------------------------------------ right.
right.
left.
exact H115.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A Q) as H117.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H117.
-------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (Q) H26).
-------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H118.
--------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q)) as H120.
---------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H118.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q A) as H118.
-------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (Q) H117).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q A E) as H119.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (Q) (A) (E)).
----------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (Q) (A) (E)).
-----------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (P) (A) (E) (Q) (A) (H113) (H114) (H116) H118).


--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A Q) as H120.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A Q E) /\ ((euclidean__axioms.nCol A E Q) /\ ((euclidean__axioms.nCol E Q A) /\ ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q))))) as H120.
----------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (Q) (A) (E) H119).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A Q E) /\ ((euclidean__axioms.nCol A E Q) /\ ((euclidean__axioms.nCol E Q A) /\ ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q))))) as H121.
------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.nCol A E Q) /\ ((euclidean__axioms.nCol E Q A) /\ ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q)))) as H123.
------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.nCol E Q A) /\ ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q))) as H125.
-------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q)) as H127.
--------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H128.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS Q A F)) as H121.
----------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Euclid5 (m) (E) (A) (B) (Q) (M) (H54) (H109) (H108) (H111) (H112) H120).
----------------------------------------------------------------------------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS Q A F))) as H122.
------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------ destruct H122 as [F H122].
assert (* AndElim *) ((euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS Q A F)) as H123.
------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (euclidean__axioms.Col E m F) as H125.
-------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H123.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E F) as H126.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H126.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (m) (F) H125).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H127.
----------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)))) as H129.
------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------ destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))) as H131.
------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)) as H133.
-------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H127.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f m) as H127.
---------------------------------------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (E) (f) (m) H107).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E f) as H128.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H128.
------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (f) (m) H127).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H129.
------------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E)))) as H131.
-------------------------------------------------------------------------------------------------------------- exact H130.
-------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))) as H133.
--------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E)) as H135.
---------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
exact H133.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H129.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H129.
------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (m) (F) H123).
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H130.
-------------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F)) as H132.
--------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
exact H132.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq m E) as H130.
------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (m) H129).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f F) as H131.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (f) (F)).
---------------------------------------------------------------------------------------------------------------intro H131.
apply (@euclidean__tactics.Col__nCol__False (E) (f) (F) (H131)).
----------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (m) (E) (f) (F) (H128) (H126) H130).


-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A F) as H132.
--------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H124.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS Q A P) as H133.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (A) (Q) H26).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A P) as H134.
----------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H133.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q A) as H135.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H135.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (A) (P) H133).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H136.
-------------------------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P)) as H138.
--------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
exact H138.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A Q) as H136.
------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A Q F) as H137.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H137.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (A) (F) H132).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H138.
---------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q)))) as H140.
----------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))) as H142.
------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q)) as H144.
------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
exact H138.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A Q P) as H138.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q))))) as H138.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (A) (P) H134).
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q))))) as H139.
----------------------------------------------------------------------------------------------------------------------- exact H138.
----------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q)))) as H141.
------------------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------------------ destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q))) as H143.
------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q)) as H145.
-------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
exact H139.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q F P) as H139.
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (Q) (F) (P)).
-----------------------------------------------------------------------------------------------------------------------intro H139.
apply (@euclidean__tactics.Col__nCol__False (Q) (F) (P) (H139)).
------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (Q) (F) (P) (H137) (H138) H136).


---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q F) as H140.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P Q F) /\ ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q))))) as H140.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (Q) (F) (P) H139).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P Q F) /\ ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q))))) as H141.
------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P Q F) /\ ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q)))) as H143.
-------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col P Q F) /\ ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q))) as H145.
--------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q)) as H147.
---------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
exact H145.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H141.
------------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq Q P) as H142.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H142.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (A) (P) H133).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H143.
--------------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P)) as H145.
---------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
exact H146.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H143.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (Q) (P) H142).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H144.
--------------------------------------------------------------------------------------------------------------------------- exists F.
split.
---------------------------------------------------------------------------------------------------------------------------- exact H141.
---------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------- exact H143.
----------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------------------------ exact H140.
--------------------------------------------------------------------------------------------------------------------------- apply (@H73 H144).
------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.CongA C E A C E f))) as H92.
------------------------------------------------------------------------- intro H92.
assert (* Cut *) (euclidean__defs.LtA C E A C E f) as H93.
-------------------------------------------------------------------------- apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 (C) (E) (A) (C) (E) (f) (H71) (H90) (H92) H74).
-------------------------------------------------------------------------- apply (@H91 H93).
------------------------------------------------------------------------- assert (* Cut *) (exists (d: euclidean__axioms.Point) (a: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)))))))) as H93.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H93.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------- assert (exists d: euclidean__axioms.Point, (exists (a: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))))))) as H94.
--------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------- destruct H94 as [d H94].
assert (exists a: euclidean__axioms.Point, (exists (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))))))) as H95.
---------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------- destruct H95 as [a H95].
assert (exists p: euclidean__axioms.Point, (exists (q: euclidean__axioms.Point), (euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))))))) as H96.
----------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------- destruct H96 as [p H96].
assert (exists q: euclidean__axioms.Point, ((euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))))))) as H97.
------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------ destruct H97 as [q H97].
assert (* AndElim *) ((euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)))))))) as H98.
------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))))) as H100.
-------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)))))) as H102.
--------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))))) as H104.
---------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)))) as H106.
----------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A))) as H108.
------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------ destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)) as H110.
------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* Cut *) (euclidean__axioms.Col P Q A) as H112.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H112.
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------------------------------- right.
right.
right.
right.
right.
exact H26.
-------------------------------------------------------------------------------------- assert (* Cut *) (d = p) as H113.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H113.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
---------------------------------------------------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (E) (C) (d) (p) (H98) (H102) H106).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong d a d q) as H114.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H114.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun d0: euclidean__axioms.Point => (euclidean__defs.Out E C d0) -> ((euclidean__axioms.Cong E d0 E p) -> ((euclidean__axioms.Cong d0 a p q) -> (euclidean__axioms.Cong d0 a d0 q))))) with (x := d).
------------------------------------------------------------------------------------------intro H115.
intro H116.
intro H117.
exact H117.

------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------ exact H110.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a d q d) as H115.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong a d q d) /\ ((euclidean__axioms.Cong a d d q) /\ (euclidean__axioms.Cong d a q d))) as H115.
------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (d) (a) (d) (q) H114).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong a d q d) /\ ((euclidean__axioms.Cong a d d q) /\ (euclidean__axioms.Cong d a q d))) as H116.
------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Cong a d d q) /\ (euclidean__axioms.Cong d a q d)) as H118.
-------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H116.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a E q E) as H116.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong a E q E) /\ ((euclidean__axioms.Cong a E E q) /\ (euclidean__axioms.Cong E a q E))) as H116.
------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (a) (E) (q) H108).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a E q E) /\ ((euclidean__axioms.Cong a E E q) /\ (euclidean__axioms.Cong E a q E))) as H117.
-------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Cong a E E q) /\ (euclidean__axioms.Cong E a q E)) as H119.
--------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
exact H117.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E d) as H117.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H117.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
-------------------------------------------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (E) (C) (d) H98).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C d) as H118.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H118.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (E) (C) (d) H98).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A f E d) as H119.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H119.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
---------------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (E) (C) (d) (A) (f) (H59) (H118) H117).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E d E) as H120.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H120.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------------------------------------- right.
left.
exact H87.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E E d) as H121.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col E E d) /\ ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E))))) as H121.
------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (d) (E) H120).
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col E E d) /\ ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E))))) as H122.
------------------------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col E E d) /\ ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E)))) as H124.
-------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col E E d) /\ ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E))) as H126.
--------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E)) as H128.
---------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H128.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A q E d) as H122.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H122.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (E) (E) (d) (A) (f) (q) (H119) (H121) H104).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS q A E d) as H123.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS q A E d) /\ ((euclidean__defs.OS A q d E) /\ (euclidean__defs.OS q A d E))) as H123.
-------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (d) (A) (q) H122).
-------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS q A E d) /\ ((euclidean__defs.OS A q d E) /\ (euclidean__defs.OS q A d E))) as H124.
--------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__defs.OS A q d E) /\ (euclidean__defs.OS q A d E)) as H126.
---------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
exact H124.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS q a E d) as H124.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H124.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (E) (E) (d) (q) (A) (a) (H123) (H121) H100).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS a q E d) as H125.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS a q E d) /\ ((euclidean__defs.OS q a d E) /\ (euclidean__defs.OS a q d E))) as H125.
---------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (d) (q) (a) H124).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS a q E d) /\ ((euclidean__defs.OS q a d E) /\ (euclidean__defs.OS a q d E))) as H126.
----------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__defs.OS q a d E) /\ (euclidean__defs.OS a q d E)) as H128.
------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
exact H126.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (a = q) as H126.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H126.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------------------------------------------- apply (@proposition__07.proposition__07 (E) (d) (a) (q) (H117) (H116) (H115) H125).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A a) as H127.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H127.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------------------------------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (E) (A) (a) H100).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f q) as H128.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H128.
------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (E) (f) (q) H104).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E A q) as H129.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H129.
-------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
-------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point q (fun a0: euclidean__axioms.Point => (euclidean__defs.Out E A a0) -> ((euclidean__axioms.Cong E a0 E q) -> ((euclidean__axioms.Cong d a0 p q) -> ((euclidean__axioms.Cong d a0 d q) -> ((euclidean__axioms.Cong a0 d q d) -> ((euclidean__axioms.Cong a0 E q E) -> ((euclidean__defs.OS q a0 E d) -> ((euclidean__defs.OS a0 q E d) -> ((euclidean__axioms.Col E A a0) -> (euclidean__axioms.Col E A q))))))))))) with (x := a).
---------------------------------------------------------------------------------------------------------intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
apply (@eq__ind__r euclidean__axioms.Point p (fun d0: euclidean__axioms.Point => (euclidean__defs.Out E C d0) -> ((euclidean__axioms.Cong E d0 E p) -> ((euclidean__axioms.Cong d0 q p q) -> ((euclidean__axioms.Cong q d0 q d0) -> ((euclidean__axioms.Cong d0 q d0 q) -> ((euclidean__axioms.neq E d0) -> ((euclidean__axioms.Col E C d0) -> ((euclidean__defs.OS A f E d0) -> ((euclidean__axioms.Col E d0 E) -> ((euclidean__axioms.Col E E d0) -> ((euclidean__defs.OS A q E d0) -> ((euclidean__defs.OS q A E d0) -> ((euclidean__defs.OS q q E d0) -> ((euclidean__defs.OS q q E d0) -> (euclidean__axioms.Col E A q)))))))))))))))) with (x := d).
----------------------------------------------------------------------------------------------------------intro H139.
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
exact H138.

---------------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------- exact H136.

--------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q E A) as H130.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E q) /\ ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))))) as H130.
--------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (q) H129).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E q) /\ ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))))) as H131.
---------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E)))) as H133.
----------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))) as H135.
------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E)) as H137.
------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H135.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q E f) as H131.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E q) /\ ((euclidean__axioms.Col f q E) /\ ((euclidean__axioms.Col q E f) /\ ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E))))) as H131.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (f) (q) H128).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col f E q) /\ ((euclidean__axioms.Col f q E) /\ ((euclidean__axioms.Col q E f) /\ ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E))))) as H132.
----------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col f q E) /\ ((euclidean__axioms.Col q E f) /\ ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E)))) as H134.
------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col q E f) /\ ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E))) as H136.
------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E)) as H138.
-------------------------------------------------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
exact H136.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E q) as H132.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H132.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (E) (f) (q) H104).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q E) as H133.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H133.
------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (q) H132).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A f) as H134.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H134.
------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (A) (f)).
--------------------------------------------------------------------------------------------------------------intro H135.
apply (@euclidean__tactics.Col__nCol__False (E) (A) (f) (H135)).
---------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (E) (A) (f) (H130) (H131) H133).


------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E f A) as H135.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E f) /\ ((euclidean__axioms.Col A f E) /\ ((euclidean__axioms.Col f E A) /\ ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E))))) as H135.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (f) H134).
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E f) /\ ((euclidean__axioms.Col A f E) /\ ((euclidean__axioms.Col f E A) /\ ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E))))) as H136.
--------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col A f E) /\ ((euclidean__axioms.Col f E A) /\ ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E)))) as H138.
---------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col f E A) /\ ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E))) as H140.
----------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E)) as H142.
------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
exact H142.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H136.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H136.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (Q) H26).
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H137.
---------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q)) as H139.
----------------------------------------------------------------------------------------------------------------- exact H138.
----------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
exact H140.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H137.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H137.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
---------------------------------------------------------------------------------------------------------------- exists A.
split.
----------------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------------- apply (@H73 H137).
------------------------------------------------------ assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F)))) as H74.
------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as H74.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) H73).
-------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as H75.
--------------------------------------------------------- exact H74.
--------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as __TmpHyp.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X))))) as H76.
----------------------------------------------------------- exact __TmpHyp.
----------------------------------------------------------- destruct H76 as [x H76].
assert (* AndElim *) ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f x) /\ (euclidean__axioms.Col P Q x)))) as H77.
------------------------------------------------------------ exact H76.
------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f x) /\ (euclidean__axioms.Col P Q x))) as H79.
------------------------------------------------------------- exact H78.
------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col E f x) /\ (euclidean__axioms.Col P Q x)) as H81.
-------------------------------------------------------------- exact H80.
-------------------------------------------------------------- destruct H81 as [H81 H82].
exists x.
split.
--------------------------------------------------------------- exact H77.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H79.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H81.
----------------------------------------------------------------- exact H82.
------------------------------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F))))) as H75.
-------------------------------------------------------- exact H74.
-------------------------------------------------------- destruct H75 as [F H75].
assert (* AndElim *) ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F)))) as H76.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F))) as H78.
---------------------------------------------------------- exact H77.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F)) as H80.
----------------------------------------------------------- exact H79.
----------------------------------------------------------- destruct H80 as [H80 H81].
assert (* Cut *) (euclidean__axioms.neq C E) as H82.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H82.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------- exact H70.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par P Q E C) as H83.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H83.
-------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (P) (Q) (E) (B) (C) (H40) (H61) H69).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E C P Q) as H84.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H84.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (P) (Q) (E) (C) H83).
-------------------------------------------------------------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__defs.PG F G C E) /\ (euclidean__axioms.Col P Q G)) as H85.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H85.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (F) (C) (E) (P) (Q) (H84) H81).
--------------------------------------------------------------- assert (exists G: euclidean__axioms.Point, ((euclidean__defs.PG F G C E) /\ (euclidean__axioms.Col P Q G))) as H86.
---------------------------------------------------------------- exact H85.
---------------------------------------------------------------- destruct H86 as [G H86].
assert (* AndElim *) ((euclidean__defs.PG F G C E) /\ (euclidean__axioms.Col P Q G)) as H87.
----------------------------------------------------------------- exact H86.
----------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* Cut *) (euclidean__defs.PG G F E C) as H89.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H89.
------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip (F) (G) (C) (E) H87).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG F E C G) as H90.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H90.
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (G) (F) (E) (C) H89).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A Q) as H91.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H91.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H26.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q A) as H92.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H92.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (Q) H91).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H93.
----------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P)))) as H95.
------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))) as H97.
------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P)) as H99.
-------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H99.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F E C G) as H93.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par F E C G) /\ (euclidean__defs.Par F G E C)) as H93.
----------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__defs.Par G F E C) /\ (euclidean__defs.Par G C F E)) as H95.
------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__defs.Par F G C E) /\ (euclidean__defs.Par F E G C)) as H97.
------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H93.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E G) as H94.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H94.
------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC (F) (E) (C) (G) H93).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H95.
------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G))) as H97.
-------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)) as H99.
--------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H100.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F G) as H95.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F)))))) as H95.
------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (F) (E) (G) H94).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F)))))) as H96.
-------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F))))) as H98.
--------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F)))) as H100.
---------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F))) as H102.
----------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F)) as H104.
------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------ destruct H104 as [H104 H105].
exact H100.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F G A) as H96.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H96.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (G) (A)).
---------------------------------------------------------------------------intro H97.
apply (@euclidean__tactics.Col__nCol__False (F) (G) (A) (H97)).
----------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (P) (Q) (F) (G) (A) (H78) (H81) (H88) H92).


------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C A E C) as H97.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H97.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------- apply (@proposition__41.proposition__41 (F) (E) (C) (G) (A) (H90) H96).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par P Q C B) as H98.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par Q P B C) /\ ((euclidean__defs.Par P Q C B) /\ (euclidean__defs.Par Q P C B))) as H98.
---------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (P) (Q) (B) (C) H40).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par Q P B C) /\ ((euclidean__defs.Par P Q C B) /\ (euclidean__defs.Par Q P C B))) as H99.
----------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__defs.Par P Q C B) /\ (euclidean__defs.Par Q P C B)) as H101.
------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------ destruct H101 as [H101 H102].
exact H101.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B E) as H99.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H99.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H61).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H100.
------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H102.
------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H104.
-------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H106.
--------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------- destruct H106 as [H106 H107].
exact H100.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H100.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H100.
------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H65).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par P Q E B) as H101.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H101.
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (P) (Q) (E) (C) (B) (H98) (H99) H100).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par P Q B E) as H102.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par Q P E B) /\ ((euclidean__defs.Par P Q B E) /\ (euclidean__defs.Par Q P B E))) as H102.
-------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (P) (Q) (E) (B) H101).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par Q P E B) /\ ((euclidean__defs.Par P Q B E) /\ (euclidean__defs.Par Q P B E))) as H103.
--------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__defs.Par P Q B E) /\ (euclidean__defs.Par Q P B E)) as H105.
---------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H105.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B E E C) as H103.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H103.
--------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (M) (M) (Q) H50).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H104.
---------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M)) as H106.
----------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------- destruct H106 as [H106 H107].
exact H20.
-------------------------------------------------------------------------------- assert (* Cut *) (E = E) as H104.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H104.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) E).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E E) as H105.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H105.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------- right.
right.
left.
exact H104.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B E A E C) as H106.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H106.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------ apply (@proposition__38.proposition__38 (A) (B) (E) (A) (E) (C) (P) (Q) (H102) (H92) (H92) (H103) (H105) H5).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C A B E) as H107.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H107.
------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (E) (A) (E) (C) H106).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A E C A E B) as H108.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET A E C B E A) /\ ((euclidean__axioms.ET A E C A E B) /\ ((euclidean__axioms.ET A E C B A E) /\ ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B))))) as H108.
-------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (E) (C) (A) (B) (E) H107).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET A E C B E A) /\ ((euclidean__axioms.ET A E C A E B) /\ ((euclidean__axioms.ET A E C B A E) /\ ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B))))) as H109.
--------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.ET A E C A E B) /\ ((euclidean__axioms.ET A E C B A E) /\ ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B)))) as H111.
---------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.ET A E C B A E) /\ ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B))) as H113.
----------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B)) as H115.
------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
exact H111.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B A E C) as H109.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H109.
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (E) (C) (A) (E) (B) H108).
-------------------------------------------------------------------------------------- assert (* Cut *) (E = E) as H110.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H110.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E E) as H111.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H111.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------- right.
right.
left.
exact H110.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H112.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))))) as H112.
------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (B) (E) (A) H66).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))))) as H113.
------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B)))) as H115.
-------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))) as H117.
--------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B)) as H119.
---------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
exact H120.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B A E C) as H113.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H113.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------- exists E.
split.
-------------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG E F G C) as H114.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H114.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip (F) (E) (C) (G) H90).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 F E C C G F) as H115.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H115.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H116.
---------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
----------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H117.
----------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------------------------------------------------------------------------------------------------ apply (@H116 (A0) (B0) (C0) (D0) __).
------------------------------------------------------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H118.
------------------------------------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------------------------------------------------------- apply (@H117 (A0) (B0) (C0) (D0) __).
------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H119.
------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------------------------------------------------------------------------------------------------- apply (@H118 (A0) (B0) (C0) (D0) __).
-------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------- apply (@H119 (E) (C) (F) (G) H114).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C C G F) as H116.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H116.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (F) (E) (C) (C) (G) (F) H115).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C F C G) as H117.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F E C G F C) /\ ((euclidean__axioms.ET F E C C F G) /\ ((euclidean__axioms.ET F E C G C F) /\ ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G))))) as H117.
----------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (E) (C) (C) (G) (F) H116).
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F E C G F C) /\ ((euclidean__axioms.ET F E C C F G) /\ ((euclidean__axioms.ET F E C G C F) /\ ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G))))) as H118.
------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.ET F E C C F G) /\ ((euclidean__axioms.ET F E C G C F) /\ ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G)))) as H120.
------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.ET F E C G C F) /\ ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G))) as H122.
-------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G)) as H124.
--------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
exact H125.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F E C) as H118.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H118.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (F) (E) (C) (F) (C) (G) H117).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F C E) as H119.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.ET F C G E C F) /\ ((euclidean__axioms.ET F C G F C E) /\ ((euclidean__axioms.ET F C G E F C) /\ ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E))))) as H119.
------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (C) (G) (F) (E) (C) H118).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F C G E C F) /\ ((euclidean__axioms.ET F C G F C E) /\ ((euclidean__axioms.ET F C G E F C) /\ ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E))))) as H120.
-------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.ET F C G F C E) /\ ((euclidean__axioms.ET F C G E F C) /\ ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E)))) as H122.
--------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.ET F C G E F C) /\ ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E))) as H124.
---------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E)) as H126.
----------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
exact H122.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F C E F C G) as H120.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H120.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (F) (C) (G) (F) (C) (E) H119).
------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS E m G) /\ (euclidean__axioms.BetS F m C)) as H121.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H121.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (E) (F) (G) (C) H114).
-------------------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS E m G) /\ (euclidean__axioms.BetS F m C))) as H122.
--------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------- destruct H122 as [m H122].
assert (* AndElim *) ((euclidean__axioms.BetS E m G) /\ (euclidean__axioms.BetS F m C)) as H123.
---------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (euclidean__axioms.Col F m C) as H125.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H125.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H124.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C m) as H126.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m F C) /\ ((euclidean__axioms.Col m C F) /\ ((euclidean__axioms.Col C F m) /\ ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F))))) as H126.
------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (m) (C) H125).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m F C) /\ ((euclidean__axioms.Col m C F) /\ ((euclidean__axioms.Col C F m) /\ ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F))))) as H127.
-------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col m C F) /\ ((euclidean__axioms.Col C F m) /\ ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F)))) as H129.
--------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col C F m) /\ ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F))) as H131.
---------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F)) as H133.
----------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H133.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par F E C G) as H127.
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E F G C) /\ (euclidean__defs.Par E C F G)) as H127.
-------------------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__defs.Par F E C G) /\ (euclidean__defs.Par F G E C)) as H129.
--------------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__defs.Par G F E C) /\ (euclidean__defs.Par G C F E)) as H131.
---------------------------------------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__defs.Par F G C E) /\ (euclidean__defs.Par F E G C)) as H133.
----------------------------------------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H93.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E C) as H128.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H128.
--------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (F) (E) (C) (G) H127).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H129.
---------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G))) as H131.
----------------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)) as H133.
------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------ destruct H133 as [H133 H134].
exact H129.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F C E) as H129.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H129.
---------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (F) (E) (C) H128).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H130.
----------------------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F)))) as H132.
------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))) as H134.
------------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F)) as H136.
-------------------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H136.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E F C G) as H130.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H130.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------------------- exists m.
split.
------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F E C) as H131.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H131.
------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (F) (E) (C) (A) (E) (C) H97).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B F E C) as H132.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H132.
------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (A) (E) (B) (F) (E) (C) (A) (E) (C) (H109) H131).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A E B F C E) as H133.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET A E B E C F) /\ ((euclidean__axioms.ET A E B F C E) /\ ((euclidean__axioms.ET A E B E F C) /\ ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E))))) as H133.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (E) (B) (F) (E) (C) H132).
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET A E B E C F) /\ ((euclidean__axioms.ET A E B F C E) /\ ((euclidean__axioms.ET A E B E F C) /\ ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E))))) as H134.
--------------------------------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.ET A E B F C E) /\ ((euclidean__axioms.ET A E B E F C) /\ ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E)))) as H136.
---------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.ET A E B E F C) /\ ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E))) as H138.
----------------------------------------------------------------------------------------------------------------- exact H137.
----------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E)) as H140.
------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
exact H136.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F E C) as H134.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H134.
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F C E) as H135.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H135.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F E C) as H136.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F C G C E F) /\ ((euclidean__axioms.ET F C G F E C) /\ ((euclidean__axioms.ET F C G C F E) /\ ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C))))) as H136.
----------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (C) (G) (F) (C) (E) H135).
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F C G C E F) /\ ((euclidean__axioms.ET F C G F E C) /\ ((euclidean__axioms.ET F C G C F E) /\ ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C))))) as H137.
------------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------------ destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.ET F C G F E C) /\ ((euclidean__axioms.ET F C G C F E) /\ ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C)))) as H139.
------------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.ET F C G C F E) /\ ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C))) as H141.
-------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C)) as H143.
--------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
exact H139.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C F C G) as H137.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H137.
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------ exact H117.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F C G) as H138.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H138.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (A) (E) (C) (F) (C) (G) (F) (E) (C) (H134) H137).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A B E C F E C G) as H139.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H139.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 (A) (E) (B) (C) (E) (F) (C) (E) (G) (m) (H133) (H138) (H19)).
---------------------------------------------------------------------------------------------------------------------right.
right.
exact H110.

--------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------left.
exact H124.

------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E C) as H140.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H140.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (F) (E) (C) (G) H127).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H141.
---------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G))) as H143.
----------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)) as H145.
------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
exact H128.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E F) as H141.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H141.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (F) (E) (C) H140).
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H142.
----------------------------------------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F)))) as H144.
------------------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))) as H146.
------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F)) as H148.
-------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
exact H149.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F C E F) as H142.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H142.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (C) (E) (F) H141).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as H143.
----------------------------------------------------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H144.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))))) as H144.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (E) (F) H141).
------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))))) as H145.
-------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C))))) as H147.
--------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))) as H149.
---------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C))) as H151.
----------------------------------------------------------------------------------------------------------------------------- exact H150.
----------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)) as H153.
------------------------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------------------------ destruct H153 as [H153 H154].
exact H153.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E F) as H145.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H145.
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (E) H144).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H146.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as H146.
--------------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as __TmpHyp.
---------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------- assert (E = f \/ (E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f))))) as H147.
----------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp.
----------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147|H147].
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H148.
------------------------------------------------------------------------------------------------------------------------------- intro H148.
apply (@H73).
--------------------------------------------------------------------------------------------------------------------------------intro H149.
apply (@H76 H147).

------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
--------------------------------------------------------------------------------------------------------------------------------intro H149.
assert (* AndElim *) ((euclidean__axioms.neq J D) /\ ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))))) as H150.
--------------------------------------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H154.
----------------------------------------------------------------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H158.
------------------------------------------------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))))) as H160.
-------------------------------------------------------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H164.
---------------------------------------------------------------------------------------------------------------------------------------- exact H60.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))))) as H166.
----------------------------------------------------------------------------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))))) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H151.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))))) as H198.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))))) as H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))))) as H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))))) as H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))))) as H212.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))) as H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))) as H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H222.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))) as H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))) as H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))) as H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [H240 H241].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))) as H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H250.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* AndElim *) ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))) as H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H254 H255].
assert (* AndElim *) ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))) as H256.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))) as H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H258 as [H258 H259].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H260.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H260 H261].
assert (* AndElim *) ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))) as H262.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [H262 H263].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))) as H264.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H264 as [H264 H265].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))) as H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H270.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))) as H272.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H274.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))) as H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H276 as [H276 H277].
assert (* AndElim *) ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))) as H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H280.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H282.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [H282 H283].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))) as H284.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H284 as [H284 H285].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H286.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H255.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H286 H287].
assert (* AndElim *) ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))) as H288.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H288 as [H288 H289].
assert (* AndElim *) ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))) as H290.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H292.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))) as H294.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [H294 H295].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))) as H296.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))) as H298.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))) as H300.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H300 as [H300 H301].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H302.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))) as H304.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H273.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H304 as [H304 H305].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H306.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H275.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H306 as [H306 H307].
assert (* AndElim *) ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))) as H308.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H277.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H308 as [H308 H309].
assert (* Cut *) (False) as H310.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H76 H147).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H311.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@H148 H149).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert False.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H311.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------------------------------------------------------------ assert (E = F \/ (f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))) as H148.
------------------------------------------------------------------------------------------------------------------------------- exact H147.
------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148|H148].
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H149.
--------------------------------------------------------------------------------------------------------------------------------- intro H149.
apply (@H73).
----------------------------------------------------------------------------------------------------------------------------------intro H150.
apply (@H145 H148).

--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
----------------------------------------------------------------------------------------------------------------------------------intro H150.
assert (* AndElim *) ((euclidean__axioms.neq J D) /\ ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))))) as H151.
----------------------------------------------------------------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H153.
------------------------------------------------------------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------------------------------------------------------------ destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H155.
------------------------------------------------------------------------------------------------------------------------------------- exact H6.
------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))))) as H157.
-------------------------------------------------------------------------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H159.
--------------------------------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))))) as H161.
---------------------------------------------------------------------------------------------------------------------------------------- exact H57.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))))) as H163.
----------------------------------------------------------------------------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))))) as H171.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))))) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))))) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H152.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H185.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H187.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))))) as H189.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))))) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))))) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H197.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))))) as H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H170.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))))) as H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))))) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))) as H215.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H217.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H219.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))) as H221.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H223.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))) as H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))) as H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))) as H231.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))) as H233.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))) as H235.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))) as H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H237 as [H237 H238].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))) as H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))) as H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))) as H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H249 as [H249 H250].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))) as H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H255.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [H255 H256].
assert (* AndElim *) ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))) as H257.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))) as H259.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H261 as [H261 H262].
assert (* AndElim *) ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))) as H263.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [H263 H264].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))) as H265.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [H265 H266].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))) as H267.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H267 as [H267 H268].
assert (* AndElim *) ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))) as H269.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H271.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))) as H273.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H273 as [H273 H274].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H275.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))) as H277.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H277 as [H277 H278].
assert (* AndElim *) ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))) as H279.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H279 as [H279 H280].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H283.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))) as H285.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H285 as [H285 H286].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* AndElim *) ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))) as H289.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [H289 H290].
assert (* AndElim *) ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))) as H291.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H291 as [H291 H292].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H293.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [H293 H294].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))) as H295.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H264.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))) as H297.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H297 as [H297 H298].
assert (* AndElim *) ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))) as H299.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))) as H301.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H270.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H301 as [H301 H302].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H303.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H272.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H303 as [H303 H304].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))) as H305.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H274.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H305 as [H305 H306].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H307.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H276.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H307 as [H307 H308].
assert (* AndElim *) ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))) as H309.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H309 as [H309 H310].
assert (* Cut *) (False) as H311.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H145 H148).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H312.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H149 H150).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H312.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

-------------------------------------------------------------------------------------------------------------------------------- assert (f = F \/ (euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f))) as H149.
--------------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149|H149].
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (F = F) as H150.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H150.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) F).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H151.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H151.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (F)).
--------------------------------------------------------------------------------------------------------------------------------------right.
left.
exact H150.

-------------------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out E F f) as H152.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point f (fun F0: euclidean__axioms.Point => (euclidean__axioms.Col E f F0) -> ((euclidean__axioms.Col P Q F0) -> ((euclidean__defs.PG F0 G C E) -> ((euclidean__defs.PG G F0 E C) -> ((euclidean__defs.PG F0 E C G) -> ((euclidean__defs.Par F0 E C G) -> ((euclidean__axioms.nCol F0 E G) -> ((euclidean__axioms.neq F0 G) -> ((euclidean__axioms.Col F0 G A) -> ((euclidean__axioms.ET F0 E C A E C) -> ((euclidean__defs.PG E F0 G C) -> ((euclidean__axioms.Cong__3 F0 E C C G F0) -> ((euclidean__axioms.ET F0 E C C G F0) -> ((euclidean__axioms.ET F0 E C F0 C G) -> ((euclidean__axioms.ET F0 C G F0 E C) -> ((euclidean__axioms.ET F0 C G F0 C E) -> ((euclidean__axioms.ET F0 C E F0 C G) -> ((euclidean__axioms.BetS F0 m C) -> ((euclidean__axioms.Col F0 m C) -> ((euclidean__axioms.Col F0 C m) -> ((euclidean__defs.Par F0 E C G) -> ((euclidean__axioms.nCol F0 E C) -> ((euclidean__axioms.nCol F0 C E) -> ((euclidean__axioms.TS E F0 C G) -> ((euclidean__axioms.ET A E C F0 E C) -> ((euclidean__axioms.ET A E B F0 E C) -> ((euclidean__axioms.ET A E B F0 C E) -> ((euclidean__axioms.ET A E C F0 E C) -> ((euclidean__axioms.ET F0 C G F0 C E) -> ((euclidean__axioms.ET F0 C G F0 E C) -> ((euclidean__axioms.ET F0 E C F0 C G) -> ((euclidean__axioms.ET A E C F0 C G) -> ((euclidean__axioms.EF A B E C F0 E C G) -> ((euclidean__axioms.nCol F0 E C) -> ((euclidean__axioms.nCol C E F0) -> ((euclidean__defs.CongA C E F0 C E F0) -> ((euclidean__axioms.neq F0 E) -> ((euclidean__axioms.neq E F0) -> ((F0 = F0) -> ((euclidean__defs.Out E F0 F0) -> (euclidean__defs.Out E F0 f)))))))))))))))))))))))))))))))))))))))))) with (y := F).
---------------------------------------------------------------------------------------------------------------------------------------intro H153.
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
intro H189.
intro H190.
intro H191.
intro H192.
assert (* Cut *) (f = f) as H193.
---------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------- exact H192.

--------------------------------------------------------------------------------------------------------------------------------------- exact H149.
--------------------------------------------------------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- exact H150.
--------------------------------------------------------------------------------------------------------------------------------------- exact H151.
------------------------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS f E F \/ (euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)) as H150.
----------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150|H150].
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H151.
------------------------------------------------------------------------------------------------------------------------------------- intro H151.
assert (* Cut *) (E = E) as H152.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C E) as H153.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H153.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------- right.
left.
exact H152.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E f) as H154.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H154.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (f) (E) (F) H150).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E C F) as H155.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol F C E) /\ ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C))))) as H155.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (C) (E) (F) H141).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol F C E) /\ ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol F C E) /\ ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C)))) as H158.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.nCol F C E) /\ ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C))) as H160.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C)) as H162.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
exact H156.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS F E C f) as H156.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H156.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------------------- exists E.
split.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS f E C F) as H157.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H157.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (E) (C) (F) (f) H156).
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A f E C) as H158.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H158.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (C) (f) (A) H18).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H159.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E)) as H161.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
exact H59.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A E C F) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H159.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (E) (C) (A) (f) (F) (H158) H157).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (j: euclidean__axioms.Point), (euclidean__axioms.BetS A j F) /\ ((euclidean__axioms.Col E C j) /\ (euclidean__axioms.nCol E C A))) as H160.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (exists j: euclidean__axioms.Point, ((euclidean__axioms.BetS A j F) /\ ((euclidean__axioms.Col E C j) /\ (euclidean__axioms.nCol E C A)))) as H161.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [j H161].
assert (* AndElim *) ((euclidean__axioms.BetS A j F) /\ ((euclidean__axioms.Col E C j) /\ (euclidean__axioms.nCol E C A))) as H162.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col E C j) /\ (euclidean__axioms.nCol E C A)) as H164.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* Cut *) (euclidean__axioms.Col A j F) as H166.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H166.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H162.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H167.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H167.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (j) (F) H162).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H168.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F)) as H170.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H169.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H170 as [H170 H171].
exact H78.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q P) as H168.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H168.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (Q) H167).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A F) as H169.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H169.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (Q) (A) (F)).
-------------------------------------------------------------------------------------------------------------------------------------------------------intro H170.
apply (@euclidean__tactics.Col__nCol__False (Q) (A) (F) (H170)).
--------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (Q) (A) (F) (H92) (H81) H167).


----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F Q) as H170.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (A) (F) H169).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H171.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q)))) as H173.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))) as H175.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q)) as H177.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col Q P A) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))))) as H171.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (A) H92).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))))) as H172.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P)))) as H174.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))) as H176.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P)) as H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H178 as [H178 H179].
exact H172.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q P F) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col Q F P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P))))) as H172.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (F) H81).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col Q F P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P))))) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col Q F P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P)))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P)) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
exact H173.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A F) as H173.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (P) (A) (F)).
-----------------------------------------------------------------------------------------------------------------------------------------------------------intro H174.
apply (@euclidean__tactics.Col__nCol__False (P) (A) (F) (H174)).
------------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (P) (A) (F) (H171) (H172) H168).


--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F P) as H174.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H174.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (F) H173).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H175.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H174.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P)))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))) as H179.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P)) as H181.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
exact H177.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F j) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col j A F) /\ ((euclidean__axioms.Col j F A) /\ ((euclidean__axioms.Col F A j) /\ ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A))))) as H175.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (j) (F) H166).
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col j A F) /\ ((euclidean__axioms.Col j F A) /\ ((euclidean__axioms.Col F A j) /\ ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A))))) as H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.Col j F A) /\ ((euclidean__axioms.Col F A j) /\ ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A)))) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.Col F A j) /\ ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A))) as H180.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A)) as H182.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
exact H182.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (j) (F) H162).
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H177.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F)) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
exact H167.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A F) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H177.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (j) (F) H162).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H178.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F)) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
exact H181.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q j) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H178.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (P) (Q) (j)).
----------------------------------------------------------------------------------------------------------------------------------------------------------------intro H179.
apply (@euclidean__tactics.Col__nCol__False (P) (Q) (j) (H179)).
-----------------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (A) (F) (P) (Q) (j) (H177) (H174) (H170) H175).


-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet P Q E C) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H179.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exists j.
split.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet P Q E C)) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H180.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H181.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [x H181].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H182.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [x0 H182].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [x1 H183].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H184.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [x2 H184].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H185.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [x3 H185].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H188.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.Col F E x) /\ ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H190.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.Col F E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H192.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H194.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.Col C G x1) /\ ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H196.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.Col C G x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H204.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H206.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [x4 H207].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [x5 H208].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [x6 H209].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [x7 H210].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [x8 H211].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.Col P Q x4) /\ ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.Col P Q x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H218.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H220.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.Col B E x6) /\ ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H222.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.Col B E x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H224.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H226 as [H226 H227].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H230.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H232.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H233.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [x9 H233].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H234 as [x10 H234].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H235.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [x11 H235].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H236.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [x12 H236].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H237 as [x13 H237].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H238.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H240.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H240 as [H240 H241].
assert (* AndElim *) ((euclidean__axioms.Col P Q x9) /\ ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H241.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H242 as [H242 H243].
assert (* AndElim *) ((euclidean__axioms.Col P Q x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H244.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H246.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((euclidean__axioms.Col E B x11) /\ ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H248.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((euclidean__axioms.Col E B x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H250.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H252.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H253.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H254 as [H254 H255].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H258.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H259.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [x14 H259].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H260.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [x15 H260].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H261 as [x16 H261].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H262.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [x17 H262].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H263.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [x18 H263].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H264.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [H264 H265].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H266.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((euclidean__axioms.Col P Q x14) /\ ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H268.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((euclidean__axioms.Col P Q x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H270.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H270 as [H270 H271].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H272.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((euclidean__axioms.Col C B x16) /\ ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H274.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H273.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((euclidean__axioms.Col C B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H276.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H275.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H276 as [H276 H277].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H278.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H277.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H280.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H279.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H282.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H281.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H282 as [H282 H283].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H284.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H284.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H285.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [x19 H285].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H286.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H285.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [x20 H286].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H287.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H286.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [x21 H287].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H288.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H288 as [x22 H288].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H289.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H288.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [x23 H289].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H290.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H289.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H292.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H291.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((euclidean__axioms.Col F E x19) /\ ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H294.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H293.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [H294 H295].
assert (* AndElim *) ((euclidean__axioms.Col F E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H296.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H295.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H298.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H297.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H298 as [H298 H299].
assert (* AndElim *) ((euclidean__axioms.Col C G x21) /\ ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H300.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H299.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H300 as [H300 H301].
assert (* AndElim *) ((euclidean__axioms.Col C G x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H302.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H301.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H304.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H303.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H304 as [H304 H305].
assert (* AndElim *) ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H306.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H305.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H306 as [H306 H307].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H308.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H307.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H308 as [H308 H309].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H310.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H310.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H311.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H311 as [x24 H311].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H312.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H311.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H312 as [x25 H312].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H313.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H312.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H313 as [x26 H313].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H314.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H313.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H314 as [x27 H314].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H315.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H314.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H315 as [x28 H315].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H316.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H315.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H316 as [H316 H317].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H318.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H317.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H318 as [H318 H319].
assert (* AndElim *) ((euclidean__axioms.Col E C x24) /\ ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H320.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H319.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H320 as [H320 H321].
assert (* AndElim *) ((euclidean__axioms.Col E C x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H322.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H321.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H322 as [H322 H323].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H324.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H323.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H324 as [H324 H325].
assert (* AndElim *) ((euclidean__axioms.Col P Q x26) /\ ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H326.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H325.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H326 as [H326 H327].
assert (* AndElim *) ((euclidean__axioms.Col P Q x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H328.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H327.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H328 as [H328 H329].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H330.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H329.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H330 as [H330 H331].
assert (* AndElim *) ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H332.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H331.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H332 as [H332 H333].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H334.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H333.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H334 as [H334 H335].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H336.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H336.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H337.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H337 as [x29 H337].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H338.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H337.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H338 as [x30 H338].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H339.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H338.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H339 as [x31 H339].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H340.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H339.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H340 as [x32 H340].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H341.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H340.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H341 as [x33 H341].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H342.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H341.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H342 as [H342 H343].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H344.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H343.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H344 as [H344 H345].
assert (* AndElim *) ((euclidean__axioms.Col P Q x29) /\ ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H346.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H345.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H346 as [H346 H347].
assert (* AndElim *) ((euclidean__axioms.Col P Q x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H348.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H347.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H348 as [H348 H349].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H350.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H349.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H350 as [H350 H351].
assert (* AndElim *) ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H352.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H351.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H352 as [H352 H353].
assert (* AndElim *) ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H354.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H353.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H354 as [H354 H355].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H356.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H355.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H356 as [H356 H357].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H358.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H357.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H358 as [H358 H359].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H360.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H359.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H360 as [H360 H361].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H362.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H362.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H363.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp7.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H363 as [x34 H363].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x34 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H364.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H363.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H364 as [x35 H364].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X x35)))))))))))) as H365.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H364.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H365 as [x36 H365].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x36 v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H366.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H365.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H366 as [x37 H366].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 X x37) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H367.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H366.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H367 as [x38 H367].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))))) as H368.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H367.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H368 as [H368 H369].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))))) as H370.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H369.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H370 as [H370 H371].
assert (* AndElim *) ((euclidean__axioms.Col P Q x34) /\ ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))) as H372.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H371.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H372 as [H372 H373].
assert (* AndElim *) ((euclidean__axioms.Col P Q x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))) as H374.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H373.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H374 as [H374 H375].
assert (* AndElim *) ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))) as H376.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H375.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H376 as [H376 H377].
assert (* AndElim *) ((euclidean__axioms.Col B C x36) /\ ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))) as H378.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H377.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H378 as [H378 H379].
assert (* AndElim *) ((euclidean__axioms.Col B C x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))) as H380.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H379.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H380 as [H380 H381].
assert (* AndElim *) ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))) as H382.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H381.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H382 as [H382 H383].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))) as H384.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H383.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H384 as [H384 H385].
assert (* AndElim *) ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)) as H386.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H385.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H386 as [H386 H387].
exact H358.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H73).
-----------------------------------------------------------------------------------------------------------------------------------------------------------------intro H181.
apply (@H180 H179).

------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
--------------------------------------------------------------------------------------------------------------------------------------intro H152.
assert (* AndElim *) ((euclidean__axioms.neq J D) /\ ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))))) as H153.
--------------------------------------------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H155.
---------------------------------------------------------------------------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H157.
----------------------------------------------------------------------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H161.
------------------------------------------------------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))))) as H163.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))))) as H165.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H167.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H60.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))))) as H169.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))))) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H177.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))))) as H179.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))))) as H181.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq J K) /\ ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))))) as H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.neq P E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq E P) /\ ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))))) as H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))))) as H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))))) as H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))))) as H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))))) as H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))))) as H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))))) as H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq D K) /\ ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))))) as H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H188.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))))) as H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H225.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))))) as H227.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))))) as H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))))) as H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))))) as H235.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))))) as H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H237 as [H237 H238].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))))) as H239.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H241.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))))) as H243.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H243 as [H243 H244].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))))) as H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))))) as H247.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((~(euclidean__axioms.BetS J D K)) /\ ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K)))) as H249.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H249 as [H249 H250].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H251.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H253.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((~(euclidean__axioms.BetS E C A)) /\ ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A)))) as H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H255 as [H255 H256].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__axioms.BetS P A E)) /\ ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E)))) as H259.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A P)) /\ ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P)))) as H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H261 as [H261 H262].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [H263 H264].
assert (* AndElim *) ((~(euclidean__axioms.BetS B E A)) /\ ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A)))) as H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [H265 H266].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E A)) /\ ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A)))) as H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H267 as [H267 H268].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E G)) /\ ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G)))) as H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((~(euclidean__axioms.BetS A E B)) /\ ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B)))) as H271.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H273.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H273 as [H273 H274].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E)))) as H275.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C)))) as H277.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H277 as [H277 H278].
assert (* AndElim *) ((~(euclidean__axioms.BetS C E F)) /\ ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F)))) as H279.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H279 as [H279 H280].
assert (* AndElim *) ((~(euclidean__axioms.BetS J K D)) /\ (~(euclidean__axioms.BetS D J K))) as H281.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H283.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H285.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [H285 H286].
assert (* AndElim *) ((~(euclidean__axioms.BetS E A C)) /\ (~(euclidean__axioms.BetS C E A))) as H287.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H256.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H289.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [H289 H290].
assert (* AndElim *) ((~(euclidean__axioms.BetS P E A)) /\ (~(euclidean__axioms.BetS A P E))) as H291.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H291 as [H291 H292].
assert (* AndElim *) ((~(euclidean__axioms.BetS E P A)) /\ (~(euclidean__axioms.BetS A E P))) as H293.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [H293 H294].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H295.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H264.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A E)) /\ (~(euclidean__axioms.BetS E B A))) as H297.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H266.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H297 as [H297 H298].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A E)) /\ (~(euclidean__axioms.BetS E C A))) as H299.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((~(euclidean__axioms.BetS F G E)) /\ (~(euclidean__axioms.BetS E F G))) as H301.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H270.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H301 as [H301 H302].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B E)) /\ (~(euclidean__axioms.BetS E A B))) as H303.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H272.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H303 as [H303 H304].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H274.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H305 as [H305 H306].
assert (* AndElim *) ((~(euclidean__axioms.BetS F E C)) /\ (~(euclidean__axioms.BetS C F E))) as H307.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H276.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H307 as [H307 H308].
assert (* AndElim *) ((~(euclidean__axioms.BetS F C E)) /\ (~(euclidean__axioms.BetS E F C))) as H309.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H278.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H309 as [H309 H310].
assert (* AndElim *) ((~(euclidean__axioms.BetS C F E)) /\ (~(euclidean__axioms.BetS E C F))) as H311.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H280.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H311 as [H311 H312].
assert (* Cut *) (False) as H313.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H151 H152).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H313.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ contradiction.

------------------------------------------------------------------------------------------------------------------------------------ assert (euclidean__axioms.BetS E f F \/ euclidean__axioms.BetS E F f) as H151.
------------------------------------------------------------------------------------------------------------------------------------- exact H150.
------------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151|H151].
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H152.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (f)).
-----------------------------------------------------------------------------------------------------------------------------------------left.
exact H151.

----------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- exact H152.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H152.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (f)).
-----------------------------------------------------------------------------------------------------------------------------------------right.
right.
exact H151.

----------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- exact H152.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F c E f) as H147.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H147.
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (C) (E) (F) (C) (E) (F) (c) (f) (H142) (H15) H146).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E C f E c) as H148.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H148.
----------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip (C) (E) (F) (c) (E) (f) H147).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E C J D K) as H149.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H149.
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (E) (C) (f) (E) (c) (J) (D) (K) (H148) H17).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F F E C) as H150.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H150.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (E) (F) H141).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E F J D K) as H151.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H151.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (C) (E) (F) (F) (E) (C) (J) (D) (K) (H150) H149).
------------------------------------------------------------------------------------------------------------------------------- exists F.
exists G.
split.
-------------------------------------------------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------- exact H151.
---------------------------------------------------------------------------------------------------------------------------------- exact H96.
Qed.
