Require Export euclidean__axioms.
Require Export lemma__3__6a.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export logic.
Definition lemma__interior5 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> ((euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong B C b c) -> ((euclidean__axioms.Cong A D a d) -> ((euclidean__axioms.Cong C D c d) -> (euclidean__axioms.Cong B D b d)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro a.
intro b.
intro c.
intro d.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (euclidean__axioms.neq B C) as H5.
- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H5.
-- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (C) H).
-- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H6.
--- exact H5.
--- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H8.
---- exact H7.
---- destruct H8 as [H8 H9].
exact H6.
- assert (* Cut *) (euclidean__axioms.neq A C) as H6.
-- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H6.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (C) H).
--- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H9.
----- exact H8.
----- destruct H9 as [H9 H10].
exact H10.
-- assert (* Cut *) (~(C = A)) as H7.
--- intro H7.
assert (* Cut *) (A = C) as H8.
---- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (C) H7).
---- apply (@H6 H8).
--- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS C A M) /\ (euclidean__axioms.Cong A M B C)) as H8.
---- apply (@lemma__extension.lemma__extension (C) (A) (B) (C) (H7) H5).
---- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS C A M) /\ (euclidean__axioms.Cong A M B C))) as H9.
----- exact H8.
----- destruct H9 as [M H9].
assert (* AndElim *) ((euclidean__axioms.BetS C A M) /\ (euclidean__axioms.Cong A M B C)) as H10.
------ exact H9.
------ destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Cong A M M A) as H12.
------- apply (@euclidean__axioms.cn__equalityreverse (A) M).
------- assert (* Cut *) (euclidean__axioms.Cong M A A M) as H13.
-------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (A) (M) (A) H12).
-------- assert (* Cut *) (euclidean__axioms.Cong M A B C) as H14.
--------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (M) (A) (A) (M) (B) (C) (H13) H11).
--------- assert (* Cut *) (euclidean__axioms.neq b c) as H15.
---------- apply (@euclidean__axioms.axiom__nocollapse (B) (C) (b) (c) (H5) H2).
---------- assert (* Cut *) (euclidean__axioms.neq a c) as H16.
----------- assert (* Cut *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a c))) as H16.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal (a) (b) (c) H0).
------------ assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a c))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a c)) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
exact H20.
----------- assert (* Cut *) (~(c = a)) as H17.
------------ intro H17.
assert (* Cut *) (a = c) as H18.
------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (a) (c) H17).
------------- apply (@H16 H18).
------------ assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS c a m) /\ (euclidean__axioms.Cong a m b c)) as H18.
------------- apply (@lemma__extension.lemma__extension (c) (a) (b) (c) (H17) H15).
------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS c a m) /\ (euclidean__axioms.Cong a m b c))) as H19.
-------------- exact H18.
-------------- destruct H19 as [m H19].
assert (* AndElim *) ((euclidean__axioms.BetS c a m) /\ (euclidean__axioms.Cong a m b c)) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.Cong m a a m) as H22.
---------------- apply (@euclidean__axioms.cn__equalityreverse (m) a).
---------------- assert (* Cut *) (euclidean__axioms.Cong m a b c) as H23.
----------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (m) (a) (a) (m) (b) (c) (H22) H21).
----------------- assert (* Cut *) (euclidean__axioms.Cong b c m a) as H24.
------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (b) (m) (a) (c) H23).
------------------ assert (* Cut *) (euclidean__axioms.Cong B C m a) as H25.
------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (b) (c) (m) (a) (H2) H24).
------------------- assert (* Cut *) (euclidean__axioms.Cong M A m a) as H26.
-------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (M) (A) (B) (C) (m) (a) (H14) H25).
-------------------- assert (* Cut *) (euclidean__axioms.Cong A C a c) as H27.
--------------------- apply (@euclidean__axioms.cn__sumofparts (A) (B) (C) (a) (b) (c) (H1) (H2) (H) H0).
--------------------- assert (* Cut *) (euclidean__axioms.Cong c a C A) as H28.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong c a C A) /\ (euclidean__axioms.Cong C A c a)) as H28.
----------------------- apply (@lemma__doublereverse.lemma__doublereverse (A) (C) (a) (c) H27).
----------------------- assert (* AndElim *) ((euclidean__axioms.Cong c a C A) /\ (euclidean__axioms.Cong C A c a)) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
exact H29.
---------------------- assert (* Cut *) (euclidean__axioms.Cong C A c a) as H29.
----------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (c) (a) (A) H28).
----------------------- assert (* Cut *) (euclidean__axioms.BetS C B A) as H30.
------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (C) H).
------------------------ assert (* Cut *) (euclidean__axioms.BetS B A M) as H31.
------------------------- apply (@lemma__3__6a.lemma__3__6a (C) (B) (A) (M) (H30) H10).
------------------------- assert (* Cut *) (euclidean__axioms.BetS c b a) as H32.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (a) (b) (c) H0).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS b a m) as H33.
--------------------------- apply (@lemma__3__6a.lemma__3__6a (c) (b) (a) (m) (H32) H20).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong A M a m) as H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong A M a m) /\ ((euclidean__axioms.Cong A M m a) /\ (euclidean__axioms.Cong M A a m))) as H34.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (A) (m) (a) H26).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A M a m) /\ ((euclidean__axioms.Cong A M m a) /\ (euclidean__axioms.Cong M A a m))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Cong A M m a) /\ (euclidean__axioms.Cong M A a m)) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
exact H35.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong D M d m) as H35.
----------------------------- apply (@euclidean__axioms.axiom__5__line (C) (A) (M) (D) (c) (a) (m) (d) (H34) (H4) (H3) (H10) (H20) H29).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS m a b) as H36.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (b) (a) (m) H33).
------------------------------ assert (* Cut *) (euclidean__axioms.BetS M A B) as H37.
------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (M) H31).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong M D m d) as H38.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M D m d) /\ ((euclidean__axioms.Cong M D d m) /\ (euclidean__axioms.Cong D M m d))) as H38.
--------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (M) (d) (m) H35).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M D m d) /\ ((euclidean__axioms.Cong M D d m) /\ (euclidean__axioms.Cong D M m d))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong M D d m) /\ (euclidean__axioms.Cong D M m d)) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
exact H39.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong D B d b) as H39.
--------------------------------- apply (@euclidean__axioms.axiom__5__line (M) (A) (B) (D) (m) (a) (b) (d) (H1) (H38) (H3) (H37) (H36) H26).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H40.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H40.
----------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (d) (b) H39).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d)) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
exact H41.
---------------------------------- exact H40.
Qed.
