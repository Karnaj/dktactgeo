Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__localextension.
Require Export lemma__partnotequalwhole.
Require Export logic.
Definition proposition__01 : forall A B, (euclidean__axioms.neq A B) -> (exists X, (euclidean__defs.equilateral A B X) /\ (euclidean__axioms.Triangle A B X)).
Proof.
intro A.
intro B.
intro H.
assert (* Cut *) (exists J, euclidean__axioms.CI J A A B) as H0.
- apply (@euclidean__axioms.postulate__Euclid3 A B H).
- destruct H0 as [J H1].
assert (* Cut *) (euclidean__axioms.neq B A) as H2.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H).
-- assert (* Cut *) (exists K, euclidean__axioms.CI K B B A) as H3.
--- apply (@euclidean__axioms.postulate__Euclid3 B A H2).
--- destruct H3 as [K H4].
assert (* Cut *) (exists D, (euclidean__axioms.BetS B A D) /\ (euclidean__axioms.Cong A D A B)) as H5.
---- apply (@lemma__localextension.lemma__localextension B A B H2 H).
---- destruct H5 as [D H6].
destruct H6 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Cong B A B A) as H9.
----- apply (@euclidean__axioms.cn__congruencereflexive B A).
----- assert (* Cut *) (euclidean__axioms.OutCirc D K) as H10.
------ exists A.
exists B.
exists B.
exists A.
split.
------- exact H4.
------- split.
-------- exact H7.
-------- exact H9.
------ assert (* Cut *) (B = B) as H11.
------- apply (@logic.eq__refl Point B).
------- assert (* Cut *) (euclidean__axioms.InCirc B K) as H12.
-------- exists A.
exists A.
exists B.
exists B.
exists A.
split.
--------- exact H4.
--------- left.
exact H11.
-------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H13.
--------- apply (@euclidean__axioms.cn__congruencereflexive A B).
--------- assert (* Cut *) (euclidean__axioms.OnCirc B J) as H14.
---------- exists A.
exists B.
exists A.
split.
----------- exact H1.
----------- exact H13.
---------- assert (* Cut *) (euclidean__axioms.OnCirc D J) as H15.
----------- exists A.
exists B.
exists A.
split.
------------ exact H1.
------------ exact H8.
----------- assert (* Cut *) (A = A) as H16.
------------ apply (@logic.eq__refl Point A).
------------ assert (* Cut *) (euclidean__axioms.InCirc A J) as H17.
------------- exists A.
exists A.
exists A.
exists A.
exists B.
split.
-------------- exact H1.
-------------- left.
exact H16.
------------- assert (* Cut *) (exists C, (euclidean__axioms.OnCirc C K) /\ (euclidean__axioms.OnCirc C J)) as H18.
-------------- apply (@euclidean__axioms.postulate__circle__circle B A A B K J B D B A H4 H12 H10 H1 H14 H15).
-------------- destruct H18 as [C H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__axioms.Cong A C A B) as H22.
--------------- apply (@euclidean__axioms.axiom__circle__center__radius A A B J C H1 H21).
--------------- assert (* Cut *) (euclidean__axioms.Cong A B A C) as H23.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A C B H22).
---------------- assert (* Cut *) (euclidean__axioms.Cong B C B A) as H24.
----------------- apply (@euclidean__axioms.axiom__circle__center__radius B B A K C H4 H20).
----------------- assert (* Cut *) (euclidean__axioms.Cong B C A B) as H25.
------------------ assert (* Cut *) ((euclidean__axioms.Cong C B A B) /\ ((euclidean__axioms.Cong C B B A) /\ (euclidean__axioms.Cong B C A B))) as H25.
------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B C B A H24).
------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H29.
------------------ assert (* Cut *) (euclidean__axioms.Cong B C A C) as H26.
------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B C A B A C H25 H23).
------------------- assert (* Cut *) (euclidean__axioms.Cong A B B C) as H27.
-------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A B C B H25).
-------------------- assert (* Cut *) (euclidean__axioms.Cong A C C A) as H28.
--------------------- apply (@euclidean__axioms.cn__equalityreverse A C).
--------------------- assert (* Cut *) (euclidean__axioms.Cong B C C A) as H29.
---------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B C A C C A H26 H28).
---------------------- assert (* Cut *) (euclidean__defs.equilateral A B C) as H30.
----------------------- split.
------------------------ exact H27.
------------------------ exact H29.
----------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H31.
------------------------ apply (@euclidean__axioms.axiom__nocollapse A B B C H H27).
------------------------ assert (* Cut *) (euclidean__axioms.neq C A) as H32.
------------------------- apply (@euclidean__axioms.axiom__nocollapse B C C A H31 H29).
------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A C B)) as H33.
-------------------------- intro H33.
assert (* Cut *) (~(euclidean__axioms.Cong A C A B)) as H34.
--------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A C B H33).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong C A A C) as H35.
---------------------------- apply (@euclidean__axioms.cn__equalityreverse C A).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong C A A B) as H36.
----------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C A A C A B H35 H22).
----------------------------- assert (euclidean__axioms.Cong A C C A) as H37 by exact H28.
assert (euclidean__axioms.Cong A C A B) as H38 by exact H22.
apply (@H34 H38).
-------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A B C)) as H34.
--------------------------- intro H34.
assert (* Cut *) (~(euclidean__axioms.Cong A B A C)) as H35.
---------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A B C H34).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C A) as H36.
----------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A B B C C A H27 H29).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong C A A C) as H37.
------------------------------ apply (@euclidean__axioms.cn__equalityreverse C A).
------------------------------ assert (euclidean__axioms.Cong A B A C) as H38 by exact H23.
apply (@H35 H38).
--------------------------- assert (* Cut *) (~(euclidean__axioms.BetS B A C)) as H35.
---------------------------- intro H35.
assert (* Cut *) (~(euclidean__axioms.Cong B A B C)) as H36.
----------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole B A C H35).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H37.
------------------------------ apply (@euclidean__axioms.cn__equalityreverse B A).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong B A B C) as H38.
------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B A A B B C H37 H27).
------------------------------- apply (@H36 H38).
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H36.
----------------------------- intro H36.
assert (* Cut *) (euclidean__axioms.neq A C) as H37.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C A H32).
------------------------------ assert ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H38 by exact H36.
destruct H38 as [H39|H39].
------------------------------- apply (@H H39).
------------------------------- destruct H39 as [H40|H40].
-------------------------------- apply (@H37 H40).
-------------------------------- destruct H40 as [H41|H41].
--------------------------------- apply (@H31 H41).
--------------------------------- destruct H41 as [H42|H42].
---------------------------------- assert (* Cut *) (False) as H43.
----------------------------------- apply (@H35 H42).
----------------------------------- contradiction H43.
---------------------------------- destruct H42 as [H43|H43].
----------------------------------- assert (* Cut *) (False) as H44.
------------------------------------ apply (@H34 H43).
------------------------------------ contradiction H44.
----------------------------------- assert (* Cut *) (False) as H44.
------------------------------------ apply (@H33 H43).
------------------------------------ contradiction H44.
----------------------------- assert (* Cut *) (euclidean__axioms.Triangle A B C) as H37.
------------------------------ apply (@euclidean__tactics.nCol__notCol A B C H36).
------------------------------ exists C.
split.
------------------------------- exact H30.
------------------------------- exact H37.
Qed.
