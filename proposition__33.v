Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalanglestransitive.
Require Export logic.
Require Export proposition__04.
Require Export proposition__27B.
Require Export proposition__29B.
Definition proposition__33 : forall A B C D M, (euclidean__defs.Par A B C D) -> ((euclidean__axioms.Cong A B C D) -> ((euclidean__axioms.BetS A M D) -> ((euclidean__axioms.BetS B M C) -> ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro M.
intro H.
intro H0.
intro H1.
intro H2.
assert (exists a b c d m, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H3 by exact H.
destruct H3 as [a H4].
destruct H4 as [b H5].
destruct H5 as [c H6].
destruct H6 as [d H7].
destruct H7 as [m H8].
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
assert (* Cut *) (euclidean__axioms.Col B M C) as H29.
- right.
right.
right.
right.
left.
exact H2.
- assert (* Cut *) (euclidean__axioms.Col B C M) as H30.
-- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H30.
--- apply (@lemma__collinearorder.lemma__collinearorder B M C H29).
--- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
-- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H31.
--- intro H31.
assert (* Cut *) (euclidean__axioms.Col A B C) as H32.
---- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H32.
----- apply (@lemma__collinearorder.lemma__collinearorder B C A H31).
----- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H37.
---- assert (* Cut *) (C = C) as H33.
----- apply (@logic.eq__refl Point C).
----- assert (* Cut *) (euclidean__axioms.Col C D C) as H34.
------ right.
left.
exact H33.
------ assert (* Cut *) (euclidean__defs.Meet A B C D) as H35.
------- exists C.
split.
-------- exact H9.
-------- split.
--------- exact H11.
--------- split.
---------- exact H32.
---------- exact H34.
------- apply (@H25 H35).
--- assert (* Cut *) (euclidean__axioms.TS A B C D) as H32.
---- exists M.
split.
----- exact H1.
----- split.
------ exact H30.
------ apply (@euclidean__tactics.nCol__notCol B C A H31).
---- assert (* Cut *) (euclidean__defs.CongA A B C B C D) as H33.
----- apply (@proposition__29B.proposition__29B A D B C H H32).
----- assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H34.
------ intro H34.
assert (* Cut *) (euclidean__axioms.Col C D B) as H35.
------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H35.
-------- apply (@lemma__collinearorder.lemma__collinearorder B C D H34).
-------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H38.
------- assert (* Cut *) (B = B) as H36.
-------- apply (@logic.eq__refl Point B).
-------- assert (* Cut *) (euclidean__axioms.Col A B B) as H37.
--------- right.
right.
left.
exact H36.
--------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H38.
---------- exists B.
split.
----------- exact H9.
----------- split.
------------ exact H11.
------------ split.
------------- exact H37.
------------- exact H35.
---------- apply (@H25 H38).
------ assert (* Cut *) (euclidean__defs.CongA B C D D C B) as H35.
------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C D).
--------apply (@euclidean__tactics.nCol__notCol B C D H34).

------- assert (* Cut *) (euclidean__defs.CongA A B C D C B) as H36.
-------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C B C D D C B H33 H35).
-------- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H37.
--------- apply (@euclidean__axioms.cn__congruencereflexive B C).
--------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H38.
---------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H38.
----------- apply (@euclidean__tactics.nCol__notCol B C A H31).
----------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H39.
------------ apply (@lemma__NCorder.lemma__NCorder B C A H38).
------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H44.
---------- assert (* Cut *) (euclidean__axioms.Cong B A C D) as H39.
----------- assert (* Cut *) ((euclidean__axioms.Cong B A D C) /\ ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C))) as H39.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip A B C D H0).
------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H42.
----------- assert (* Cut *) (euclidean__axioms.Cong B C C B) as H40.
------------ assert (* Cut *) ((euclidean__axioms.Cong C B C B) /\ ((euclidean__axioms.Cong C B B C) /\ (euclidean__axioms.Cong B C C B))) as H40.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip B C B C H37).
------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H44.
------------ assert (* Cut *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H41.
------------- apply (@proposition__04.proposition__04 B A C C D B H39 H40 H36).
------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H42.
-------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H46.
--------------- apply (@lemma__NCorder.lemma__NCorder A B C H38).
--------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H53.
-------------- assert (* Cut *) (euclidean__defs.CongA A C B B C A) as H43.
--------------- destruct H41 as [H43 H44].
destruct H44 as [H45 H46].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A C B H42).
--------------- assert (* Cut *) (euclidean__defs.CongA A C B C B D) as H44.
---------------- destruct H41 as [H44 H45].
destruct H45 as [H46 H47].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A C B B C A C B D H43 H47).
---------------- assert (* Cut *) (euclidean__axioms.Cong A C B D) as H45.
----------------- destruct H41 as [H45 H46].
destruct H46 as [H47 H48].
assert (* Cut *) ((euclidean__axioms.Cong C A B D) /\ ((euclidean__axioms.Cong C A D B) /\ (euclidean__axioms.Cong A C B D))) as H49.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A C D B H45).
------------------ destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
----------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H46.
------------------ destruct H41 as [H46 H47].
destruct H47 as [H48 H49].
assert (* Cut *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H50.
------------------- apply (@lemma__collinearorder.lemma__collinearorder B C M H30).
------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H51.
------------------ assert (* Cut *) (euclidean__axioms.nCol C B A) as H47.
------------------- destruct H41 as [H47 H48].
destruct H48 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H51.
-------------------- apply (@lemma__NCorder.lemma__NCorder A C B H42).
-------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H54.
------------------- assert (* Cut *) (euclidean__axioms.TS A C B D) as H48.
-------------------- exists M.
split.
--------------------- exact H1.
--------------------- split.
---------------------- exact H46.
---------------------- exact H47.
-------------------- assert (* Cut *) (euclidean__defs.Par A C B D) as H49.
--------------------- destruct H41 as [H49 H50].
destruct H50 as [H51 H52].
apply (@proposition__27B.proposition__27B A D C B H44 H48).
--------------------- split.
---------------------- exact H49.
---------------------- exact H45.
Qed.
