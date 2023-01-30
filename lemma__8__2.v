Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__04.
Definition lemma__8__2 : forall A B C, (euclidean__defs.Per A B C) -> (euclidean__defs.Per C B A).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (exists D, (euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H0 by exact H.
destruct H0 as [D H1].
destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.neq C B) as H8.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H7).
- assert (* Cut *) (exists E, (euclidean__axioms.BetS C B E) /\ (euclidean__axioms.Cong B E B C)) as H9.
-- apply (@lemma__extension.lemma__extension C B B C H8 H7).
-- destruct H9 as [E H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__axioms.neq A B) as H13.
--- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H13.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A B D H2).
---- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
--- assert (* Cut *) (euclidean__axioms.neq B A) as H14.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H13).
---- assert (* Cut *) (C = C) as H15.
----- apply (@logic.eq__refl Point C).
----- assert (* Cut *) (A = A) as H16.
------ apply (@logic.eq__refl Point A).
------ assert (* Cut *) (euclidean__defs.Out B C C) as H17.
------- apply (@lemma__ray4.lemma__ray4 B C C).
--------right.
left.
exact H15.

-------- exact H7.
------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H18.
-------- apply (@lemma__rightangleNC.lemma__rightangleNC A B C H).
-------- assert (* Cut *) (euclidean__defs.Supp A B C C D) as H19.
--------- split.
---------- exact H17.
---------- exact H2.
--------- assert (* Cut *) (euclidean__defs.Out B A A) as H20.
---------- apply (@lemma__ray4.lemma__ray4 B A A).
-----------right.
left.
exact H16.

----------- exact H14.
---------- assert (* Cut *) (euclidean__defs.Supp C B A A E) as H21.
----------- split.
------------ exact H20.
------------ exact H11.
----------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H22.
------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A B C H18).
------------ assert (* Cut *) (euclidean__defs.CongA C B D A B E) as H23.
------------- apply (@lemma__supplements.lemma__supplements A B C C D C B A A E H22 H19 H21).
------------- assert (* Cut *) (euclidean__axioms.Cong B C B E) as H24.
-------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B B E C H12).
-------------- assert (* Cut *) (euclidean__axioms.Cong B D B A) as H25.
--------------- assert (* Cut *) ((euclidean__axioms.Cong B D B A) /\ (euclidean__axioms.Cong B A B D)) as H25.
---------------- apply (@lemma__doublereverse.lemma__doublereverse A B D B H4).
---------------- destruct H25 as [H26 H27].
exact H26.
--------------- assert (* Cut *) (~(euclidean__axioms.Col E B A)) as H26.
---------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col C B E) as H27.
----------------- right.
right.
right.
right.
left.
exact H11.
----------------- assert (* Cut *) (euclidean__axioms.Col E B C) as H28.
------------------ assert (* Cut *) ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col B E C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C E B) /\ (euclidean__axioms.Col E B C))))) as H28.
------------------- apply (@lemma__collinearorder.lemma__collinearorder C B E H27).
------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H36.
------------------ assert (* Cut *) (euclidean__axioms.neq B E) as H29.
------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C E))) as H29.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C B E H11).
-------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H30.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B E H29).
-------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H31.
--------------------- apply (@euclidean__tactics.not__nCol__Col B A C).
----------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False B A C H31).
-----------------------apply (@lemma__collinear4.lemma__collinear4 E B A C H26 H28 H30).


--------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H32.
---------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H32.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H31).
----------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H33.
---------------------- apply (@euclidean__tactics.Col__nCol__False A B C H18 H32).
---------------- assert (* Cut *) (~(euclidean__axioms.Col A B E)) as H27.
----------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col E B A) as H28.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H28.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A B E H27).
------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H36.
------------------ apply (@H26 H28).
----------------- assert (* Cut *) (euclidean__defs.CongA A B E E B A) as H28.
------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A B E).
-------------------apply (@euclidean__tactics.nCol__notCol A B E H27).

------------------ assert (* Cut *) (euclidean__defs.CongA C B D E B A) as H29.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive C B D A B E E B A H23 H28).
------------------- assert (* Cut *) ((euclidean__axioms.Cong C D E A) /\ ((euclidean__defs.CongA B C D B E A) /\ (euclidean__defs.CongA B D C B A E))) as H30.
-------------------- apply (@proposition__04.proposition__04 B C D B E A H24 H25 H29).
-------------------- assert (* Cut *) (euclidean__axioms.Cong A C C D) as H31.
--------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H35.
---------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A C D C H6).
---------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H39.
--------------------- assert (* Cut *) (euclidean__axioms.Cong A C E A) as H32.
---------------------- destruct H30 as [H32 H33].
destruct H33 as [H34 H35].
apply (@lemma__congruencetransitive.lemma__congruencetransitive A C C D E A H31 H32).
---------------------- assert (* Cut *) (euclidean__axioms.Cong C A E A) as H33.
----------------------- destruct H30 as [H33 H34].
destruct H34 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.Cong C A A E) /\ ((euclidean__axioms.Cong C A E A) /\ (euclidean__axioms.Cong A C A E))) as H37.
------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A C E A H32).
------------------------ destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H40.
----------------------- assert (* Cut *) (euclidean__axioms.Cong C B E B) as H34.
------------------------ destruct H30 as [H34 H35].
destruct H35 as [H36 H37].
assert (* Cut *) ((euclidean__axioms.Cong C B E B) /\ ((euclidean__axioms.Cong C B B E) /\ (euclidean__axioms.Cong B C E B))) as H38.
------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B C B E H24).
------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H39.
------------------------ assert (* Cut *) (euclidean__axioms.neq B A) as H35.
------------------------- destruct H30 as [H35 H36].
destruct H36 as [H37 H38].
exact H14.
------------------------- assert (* Cut *) (euclidean__defs.Per C B A) as H36.
-------------------------- exists E.
split.
--------------------------- exact H11.
--------------------------- split.
---------------------------- exact H34.
---------------------------- split.
----------------------------- exact H33.
----------------------------- exact H35.
-------------------------- exact H36.
Qed.
