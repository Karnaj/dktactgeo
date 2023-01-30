Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCdistinct.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__differenceofparts.
Require Export logic.
Require Export proposition__01.
Definition proposition__02 : forall A B C, (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq B C) -> (exists X, euclidean__axioms.Cong A X B C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) (exists D, (euclidean__defs.equilateral A B D) /\ (euclidean__axioms.Triangle A B D)) as H1.
- apply (@proposition__01.proposition__01 A B H).
- destruct H1 as [D H2].
destruct H2 as [H3 H4].
assert (* Cut *) (euclidean__axioms.Cong A B B D) as H5.
-- destruct H3 as [H5 H6].
exact H5.
-- assert (* Cut *) (euclidean__axioms.Cong B D A B) as H6.
--- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B A B D H5).
--- assert (* Cut *) (euclidean__axioms.Cong B D B A) as H7.
---- assert (* Cut *) ((euclidean__axioms.Cong D B B A) /\ ((euclidean__axioms.Cong D B A B) /\ (euclidean__axioms.Cong B D B A))) as H7.
----- apply (@lemma__congruenceflip.lemma__congruenceflip B D A B H6).
----- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H11.
---- assert (* Cut *) (euclidean__axioms.Cong B D D A) as H8.
----- destruct H3 as [H8 H9].
exact H9.
----- assert (euclidean__axioms.nCol A B D) as H9 by exact H4.
assert (* Cut *) (B = B) as H10.
------ apply (@logic.eq__refl Point B).
------ assert (* Cut *) (exists J, euclidean__axioms.CI J B B C) as H11.
------- apply (@euclidean__axioms.postulate__Euclid3 B C H0).
------- destruct H11 as [J H12].
assert (* Cut *) (euclidean__axioms.InCirc B J) as H13.
-------- exists A.
exists A.
exists B.
exists B.
exists C.
split.
--------- exact H12.
--------- left.
exact H10.
-------- assert (* Cut *) (euclidean__axioms.neq D B) as H14.
--------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H14.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct A B D H9).
---------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H23.
--------- assert (* Cut *) (exists P G, (euclidean__axioms.Col D B P) /\ ((euclidean__axioms.BetS D B G) /\ ((euclidean__axioms.OnCirc P J) /\ ((euclidean__axioms.OnCirc G J) /\ (euclidean__axioms.BetS P B G))))) as H15.
---------- apply (@euclidean__axioms.postulate__line__circle D B B J B C H12 H13 H14).
---------- destruct H15 as [P H16].
destruct H16 as [G H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.neq D G) as H26.
----------- assert (* Cut *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D G))) as H26.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal D B G H20).
------------ destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H30.
----------- assert (* Cut *) (exists R, euclidean__axioms.CI R D D G) as H27.
------------ apply (@euclidean__axioms.postulate__Euclid3 D G H26).
------------ destruct H27 as [R H28].
assert (* Cut *) (euclidean__axioms.Cong B G B C) as H29.
------------- apply (@euclidean__axioms.axiom__circle__center__radius B B C J G H12 H24).
------------- assert (* Cut *) (euclidean__axioms.Cong B C B G) as H30.
-------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B B G C H29).
-------------- assert (* Cut *) (D = D) as H31.
--------------- apply (@logic.eq__refl Point D).
--------------- assert (* Cut *) (euclidean__axioms.Cong D A B D) as H32.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D B D A H8).
---------------- assert (* Cut *) (euclidean__axioms.Cong D A D B) as H33.
----------------- assert (* Cut *) ((euclidean__axioms.Cong A D D B) /\ ((euclidean__axioms.Cong A D B D) /\ (euclidean__axioms.Cong D A D B))) as H33.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip D A B D H32).
------------------ destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H37.
----------------- assert (* Cut *) (euclidean__axioms.Cong D G D G) as H34.
------------------ apply (@euclidean__axioms.cn__congruencereflexive D G).
------------------ assert (* Cut *) (euclidean__axioms.InCirc A R) as H35.
------------------- exists G.
exists B.
exists D.
exists D.
exists G.
split.
-------------------- exact H28.
-------------------- right.
split.
--------------------- exact H20.
--------------------- split.
---------------------- exact H34.
---------------------- exact H33.
------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H36.
-------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H36.
--------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B D H9).
--------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H46.
-------------------- assert (* Cut *) (exists Q L, (euclidean__axioms.Col D A Q) /\ ((euclidean__axioms.BetS D A L) /\ ((euclidean__axioms.OnCirc Q R) /\ ((euclidean__axioms.OnCirc L R) /\ (euclidean__axioms.BetS Q A L))))) as H37.
--------------------- apply (@euclidean__axioms.postulate__line__circle D A D R D G H28 H35 H36).
--------------------- destruct H37 as [Q H38].
destruct H38 as [L H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
assert (* Cut *) (euclidean__axioms.Cong D L D G) as H48.
---------------------- apply (@euclidean__axioms.axiom__circle__center__radius D D G R L H28 H46).
---------------------- assert (* Cut *) (euclidean__axioms.Cong D B D B) as H49.
----------------------- apply (@euclidean__axioms.cn__congruencereflexive D B).
----------------------- assert (* Cut *) (euclidean__axioms.Cong D B D A) as H50.
------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D D A B H33).
------------------------ assert (* Cut *) (euclidean__axioms.Cong D G D L) as H51.
------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D D L G H48).
------------------------- assert (* Cut *) (euclidean__axioms.Cong B G A L) as H52.
-------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts D B G D A L H50 H51 H20 H42).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A L B C) as H53.
--------------------------- apply (@euclidean__axioms.cn__congruencetransitive A L B C B G H52 H29).
--------------------------- exists L.
exact H53.
Qed.
