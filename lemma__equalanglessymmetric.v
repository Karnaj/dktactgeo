Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinearitypreserved.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__doublereverse.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray2.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__equalanglessymmetric : forall A B C a b c, (euclidean__defs.CongA A B C a b c) -> (euclidean__defs.CongA a b c A B C).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H0 by exact H.
destruct H0 as [U H1].
destruct H1 as [V H2].
destruct H2 as [u H3].
destruct H3 as [v H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
assert (* Cut *) (euclidean__axioms.Cong b u B U) as H19.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B U u H13).
- assert (* Cut *) (euclidean__axioms.Cong b v B V) as H20.
-- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B V v H15).
-- assert (* Cut *) (euclidean__axioms.Cong v u V U) as H21.
--- assert (* Cut *) ((euclidean__axioms.Cong v u V U) /\ (euclidean__axioms.Cong V U v u)) as H21.
---- apply (@lemma__doublereverse.lemma__doublereverse U V u v H17).
---- destruct H21 as [H22 H23].
exact H22.
--- assert (* Cut *) (~(euclidean__axioms.Col a b c)) as H22.
---- intro H22.
assert (* Cut *) (euclidean__axioms.Col b a u) as H23.
----- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear b a u H9).
----- assert (* Cut *) (euclidean__axioms.Col b c v) as H24.
------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear b c v H11).
------ assert (* Cut *) (euclidean__axioms.Col B A U) as H25.
------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B A U H5).
------- assert (* Cut *) (euclidean__axioms.Col B C V) as H26.
-------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B C V H7).
-------- assert (* Cut *) (euclidean__axioms.Col a b u) as H27.
--------- assert (* Cut *) ((euclidean__axioms.Col a b u) /\ ((euclidean__axioms.Col a u b) /\ ((euclidean__axioms.Col u b a) /\ ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b))))) as H27.
---------- apply (@lemma__collinearorder.lemma__collinearorder b a u H23).
---------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H28.
--------- assert (* Cut *) (euclidean__axioms.neq b a) as H28.
---------- apply (@lemma__ray2.lemma__ray2 b a u H9).
---------- assert (* Cut *) (euclidean__axioms.neq a b) as H29.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric b a H28).
----------- assert (* Cut *) (euclidean__axioms.Col b u c) as H30.
------------ apply (@euclidean__tactics.not__nCol__Col b u c).
-------------intro H30.
apply (@euclidean__tactics.Col__nCol__False b u c H30).
--------------apply (@lemma__collinear4.lemma__collinear4 a b u c H27 H22 H29).


------------ assert (* Cut *) (euclidean__axioms.Col c b u) as H31.
------------- assert (* Cut *) ((euclidean__axioms.Col u b c) /\ ((euclidean__axioms.Col u c b) /\ ((euclidean__axioms.Col c b u) /\ ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b))))) as H31.
-------------- apply (@lemma__collinearorder.lemma__collinearorder b u c H30).
-------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H36.
------------- assert (* Cut *) (euclidean__axioms.Col c b v) as H32.
-------------- assert (* Cut *) ((euclidean__axioms.Col c b v) /\ ((euclidean__axioms.Col c v b) /\ ((euclidean__axioms.Col v b c) /\ ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b))))) as H32.
--------------- apply (@lemma__collinearorder.lemma__collinearorder b c v H24).
--------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H33.
-------------- assert (* Cut *) (euclidean__axioms.neq b c) as H33.
--------------- apply (@lemma__ray2.lemma__ray2 b c v H11).
--------------- assert (* Cut *) (euclidean__axioms.neq c b) as H34.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric b c H33).
---------------- assert (* Cut *) (euclidean__axioms.Col b u v) as H35.
----------------- apply (@euclidean__tactics.not__nCol__Col b u v).
------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False b u v H35).
-------------------apply (@lemma__collinear4.lemma__collinear4 c b u v H31 H32 H34).


----------------- assert (* Cut *) (euclidean__axioms.Cong u v U V) as H36.
------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric u U V v H17).
------------------ assert (* Cut *) (euclidean__axioms.Col B U V) as H37.
------------------- apply (@euclidean__tactics.not__nCol__Col B U V).
--------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False B U V H37).
---------------------apply (@lemma__collinearitypreserved.lemma__collinearitypreserved b u v B U V H35 H19 H20 H36).


------------------- assert (* Cut *) (euclidean__axioms.Col U B V) as H38.
-------------------- assert (* Cut *) ((euclidean__axioms.Col U B V) /\ ((euclidean__axioms.Col U V B) /\ ((euclidean__axioms.Col V B U) /\ ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B))))) as H38.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder B U V H37).
--------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H39.
-------------------- assert (* Cut *) (euclidean__axioms.Col U B A) as H39.
--------------------- assert (* Cut *) ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))))) as H39.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B A U H25).
---------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H44.
--------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H40.
---------------------- apply (@lemma__raystrict.lemma__raystrict B A U H5).
---------------------- assert (* Cut *) (euclidean__axioms.neq U B) as H41.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B U H40).
----------------------- assert (* Cut *) (euclidean__axioms.Col B V A) as H42.
------------------------ apply (@euclidean__tactics.not__nCol__Col B V A).
-------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False B V A H42).
--------------------------apply (@lemma__collinear4.lemma__collinear4 U B V A H38 H39 H41).


------------------------ assert (* Cut *) (euclidean__axioms.Col V B A) as H43.
------------------------- assert (* Cut *) ((euclidean__axioms.Col V B A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B))))) as H43.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder B V A H42).
-------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H44.
------------------------- assert (* Cut *) (euclidean__axioms.Col V B C) as H44.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col C B V) /\ ((euclidean__axioms.Col C V B) /\ ((euclidean__axioms.Col V B C) /\ ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B))))) as H44.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C V H26).
--------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
-------------------------- assert (* Cut *) (euclidean__axioms.neq B V) as H45.
--------------------------- apply (@lemma__raystrict.lemma__raystrict B C V H7).
--------------------------- assert (* Cut *) (euclidean__axioms.neq V B) as H46.
---------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B V H45).
---------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H47.
----------------------------- apply (@euclidean__tactics.not__nCol__Col B A C).
------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False B A C H47).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 V B A C H43 H44 H46).


----------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H48.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H48.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H47).
------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
------------------------------ apply (@euclidean__tactics.Col__nCol__False A B C H18 H48).
---- assert (* Cut *) (euclidean__axioms.Cong u v U V) as H23.
----- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric u U V v H17).
----- assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H24.
------ exists u.
exists v.
exists U.
exists V.
split.
------- exact H9.
------- split.
-------- exact H11.
-------- split.
--------- exact H5.
--------- split.
---------- exact H7.
---------- split.
----------- exact H19.
----------- split.
------------ exact H20.
------------ split.
------------- exact H23.
------------- apply (@euclidean__tactics.nCol__notCol a b c H22).
------ exact H24.
Qed.
