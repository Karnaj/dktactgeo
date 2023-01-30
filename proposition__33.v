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
Definition proposition__33 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__axioms.Cong A B C D) -> ((euclidean__axioms.BetS A M D) -> ((euclidean__axioms.BetS B M C) -> ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D))))).
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
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H3.
- exact H.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H4.
-- exact H3.
-- destruct H4 as [a H4].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H5.
--- exact H4.
--- destruct H5 as [b H5].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H6.
---- exact H5.
---- destruct H6 as [c H6].
assert (exists d: euclidean__axioms.Point, (exists (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H7.
----- exact H6.
----- destruct H7 as [d H7].
assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H8.
------ exact H7.
------ destruct H8 as [m H8].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))) as H17.
----------- exact H16.
----------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))) as H21.
------------- exact H20.
------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))) as H23.
-------------- exact H22.
-------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)) as H27.
---------------- exact H26.
---------------- destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.Col B M C) as H29.
----------------- right.
right.
right.
right.
left.
exact H2.
----------------- assert (* Cut *) (euclidean__axioms.Col B C M) as H30.
------------------ assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H30.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (C) H29).
------------------- assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H31.
-------------------- exact H30.
-------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)))) as H33.
--------------------- exact H32.
--------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))) as H35.
---------------------- exact H34.
---------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)) as H37.
----------------------- exact H36.
----------------------- destruct H37 as [H37 H38].
exact H37.
------------------ assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H31.
------------------- intro H31.
assert (* Cut *) (euclidean__axioms.Col A B C) as H32.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H32.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H31).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H35.
----------------------- exact H34.
----------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H37.
------------------------ exact H36.
------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H39.
------------------------- exact H38.
------------------------- destruct H39 as [H39 H40].
exact H37.
-------------------- assert (* Cut *) (C = C) as H33.
--------------------- apply (@logic.eq__refl (Point) C).
--------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H34.
---------------------- right.
left.
exact H33.
---------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H35.
----------------------- exists C.
split.
------------------------ exact H9.
------------------------ split.
------------------------- exact H11.
------------------------- split.
-------------------------- exact H32.
-------------------------- exact H34.
----------------------- apply (@H25 H35).
------------------- assert (* Cut *) (euclidean__axioms.TS A B C D) as H32.
-------------------- exists M.
split.
--------------------- exact H1.
--------------------- split.
---------------------- exact H30.
---------------------- apply (@euclidean__tactics.nCol__notCol (B) (C) (A) H31).
-------------------- assert (* Cut *) (euclidean__defs.CongA A B C B C D) as H33.
--------------------- apply (@proposition__29B.proposition__29B (A) (D) (B) (C) (H) H32).
--------------------- assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H34.
---------------------- intro H34.
assert (* Cut *) (euclidean__axioms.Col C D B) as H35.
----------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H35.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H34).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H38.
-------------------------- exact H37.
-------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H40.
--------------------------- exact H39.
--------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H42.
---------------------------- exact H41.
---------------------------- destruct H42 as [H42 H43].
exact H38.
----------------------- assert (* Cut *) (B = B) as H36.
------------------------ apply (@logic.eq__refl (Point) B).
------------------------ assert (* Cut *) (euclidean__axioms.Col A B B) as H37.
------------------------- right.
right.
left.
exact H36.
------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H38.
-------------------------- exists B.
split.
--------------------------- exact H9.
--------------------------- split.
---------------------------- exact H11.
---------------------------- split.
----------------------------- exact H37.
----------------------------- exact H35.
-------------------------- apply (@H25 H38).
---------------------- assert (* Cut *) (euclidean__defs.CongA B C D D C B) as H35.
----------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (C) (D)).
------------------------apply (@euclidean__tactics.nCol__notCol (B) (C) (D) H34).

----------------------- assert (* Cut *) (euclidean__defs.CongA A B C D C B) as H36.
------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (B) (C) (D) (D) (C) (B) (H33) H35).
------------------------ assert (* Cut *) (euclidean__axioms.Cong B C B C) as H37.
------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) C).
------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H38.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H38.
--------------------------- apply (@euclidean__tactics.nCol__notCol (B) (C) (A) H31).
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H39.
---------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (A) H38).
---------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)) as H46.
-------------------------------- exact H45.
-------------------------------- destruct H46 as [H46 H47].
exact H44.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong B A C D) as H39.
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A D C) /\ ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C))) as H39.
---------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (C) (D) H0).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A D C) /\ ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C)) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
exact H42.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B C C B) as H40.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong C B C B) /\ ((euclidean__axioms.Cong C B B C) /\ (euclidean__axioms.Cong B C C B))) as H40.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (B) (C) H37).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B C B) /\ ((euclidean__axioms.Cong C B B C) /\ (euclidean__axioms.Cong B C C B))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Cong C B B C) /\ (euclidean__axioms.Cong B C C B)) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
exact H44.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H41.
----------------------------- apply (@proposition__04.proposition__04 (B) (A) (C) (C) (D) (B) (H39) (H40) H36).
----------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H42.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H42.
------------------------------- exact H41.
------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H44.
-------------------------------- exact H43.
-------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H46.
--------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H38).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H47.
---------------------------------- exact H46.
---------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H49.
----------------------------------- exact H48.
----------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H51.
------------------------------------ exact H50.
------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H53.
------------------------------------- exact H52.
------------------------------------- destruct H53 as [H53 H54].
exact H53.
------------------------------ assert (* Cut *) (euclidean__defs.CongA A C B B C A) as H43.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H43.
-------------------------------- exact H41.
-------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H45.
--------------------------------- exact H44.
--------------------------------- destruct H45 as [H45 H46].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (C) (B) H42).
------------------------------- assert (* Cut *) (euclidean__defs.CongA A C B C B D) as H44.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H44.
--------------------------------- exact H41.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (C) (B) (B) (C) (A) (C) (B) (D) (H43) H47).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C B D) as H45.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H45.
---------------------------------- exact H41.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* Cut *) ((euclidean__axioms.Cong C A B D) /\ ((euclidean__axioms.Cong C A D B) /\ (euclidean__axioms.Cong A C B D))) as H49.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (D) (B) H45).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C A B D) /\ ((euclidean__axioms.Cong C A D B) /\ (euclidean__axioms.Cong A C B D))) as H50.
------------------------------------- exact H49.
------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Cong C A D B) /\ (euclidean__axioms.Cong A C B D)) as H52.
-------------------------------------- exact H51.
-------------------------------------- destruct H52 as [H52 H53].
exact H53.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H46.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H46.
----------------------------------- exact H41.
----------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H48.
------------------------------------ exact H47.
------------------------------------ destruct H48 as [H48 H49].
assert (* Cut *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H50.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (M) H30).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)))) as H53.
--------------------------------------- exact H52.
--------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))) as H55.
---------------------------------------- exact H54.
---------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)) as H57.
----------------------------------------- exact H56.
----------------------------------------- destruct H57 as [H57 H58].
exact H51.
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H47.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H47.
------------------------------------ exact H41.
------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H49.
------------------------------------- exact H48.
------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H51.
-------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H42).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H54.
---------------------------------------- exact H53.
---------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H56.
----------------------------------------- exact H55.
----------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H58.
------------------------------------------ exact H57.
------------------------------------------ destruct H58 as [H58 H59].
exact H54.
----------------------------------- assert (* Cut *) (euclidean__axioms.TS A C B D) as H48.
------------------------------------ exists M.
split.
------------------------------------- exact H1.
------------------------------------- split.
-------------------------------------- exact H46.
-------------------------------------- exact H47.
------------------------------------ assert (* Cut *) (euclidean__defs.Par A C B D) as H49.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D B) /\ ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D))) as H49.
-------------------------------------- exact H41.
-------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.CongA B A C C D B) /\ (euclidean__defs.CongA B C A C B D)) as H51.
--------------------------------------- exact H50.
--------------------------------------- destruct H51 as [H51 H52].
apply (@proposition__27B.proposition__27B (A) (D) (C) (B) (H44) H48).
------------------------------------- split.
-------------------------------------- exact H49.
-------------------------------------- exact H45.
Qed.
