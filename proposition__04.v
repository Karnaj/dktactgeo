Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__differenceofparts.
Require Export lemma__equalanglesNC.
Require Export lemma__inequalitysymmetric.
Require Export lemma__interior5.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__partnotequalwhole.
Require Export lemma__ray1.
Require Export lemma__ray2.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Definition proposition__04 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong A C a c) -> ((euclidean__defs.CongA B A C b a c) -> ((euclidean__axioms.Cong B C b c) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA A C B a c b))))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.nCol b a c) as H2.
- apply (@euclidean__tactics.nCol__notCol (b) (a) (c)).
--apply (@euclidean__tactics.nCol__not__Col (b) (a) (c)).
---apply (@lemma__equalanglesNC.lemma__equalanglesNC (B) (A) (C) (b) (a) (c) H1).


- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C)))))))) as H3.
-- exact H1.
-- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))))))) as H4.
--- exact H3.
--- destruct H4 as [U H4].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))))))) as H5.
---- exact H4.
---- destruct H5 as [V H5].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))))))) as H6.
----- exact H5.
----- destruct H6 as [u H6].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))))))) as H7.
------ exact H6.
------ destruct H7 as [v H7].
assert (* AndElim *) ((euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C)))))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Out A C V) /\ ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Out a b u) /\ ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C)))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Out a c v) /\ ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong A U a u) /\ ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C)))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A V a v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A C)) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.neq a b) as H22.
-------------- apply (@lemma__ray2.lemma__ray2 (a) (b) (u) H12).
-------------- assert (* Cut *) (euclidean__axioms.neq b a) as H23.
--------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (a) (b) H22).
--------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H24.
---------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col B A C) as H25.
----------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H25.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H24).
------------------ assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [H32 H33].
exact H26.
----------------- apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H21) H25).
---------------- assert (* Cut *) (~(A = B)) as H25.
----------------- intro H25.
assert (* Cut *) (euclidean__axioms.Col A B C) as H26.
------------------ left.
exact H25.
------------------ assert (* Cut *) (euclidean__axioms.Col B A C) as H27.
------------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H27.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H26).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
exact H28.
------------------- apply (@H24 H26).
----------------- assert (* Cut *) (~(A = C)) as H26.
------------------ intro H26.
assert (* Cut *) (euclidean__axioms.Col A B C) as H27.
------------------- right.
left.
exact H26.
------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H28.
-------------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H28.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H27).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
exact H29.
-------------------- apply (@H24 H27).
------------------ assert (* Cut *) (euclidean__axioms.neq C A) as H27.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H26).
------------------- assert (* Cut *) (~(a = c)) as H28.
-------------------- intro H28.
assert (* Cut *) (euclidean__axioms.Col b a c) as H29.
--------------------- right.
right.
left.
exact H28.
--------------------- apply (@H24).
----------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
-----------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (b) (a) (c) (H2) H29).


-------------------- assert (* Cut *) (euclidean__axioms.neq c a) as H29.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (a) (c) H28).
--------------------- assert (* Cut *) (~(b = c)) as H30.
---------------------- intro H30.
assert (* Cut *) (euclidean__axioms.Col b a c) as H31.
----------------------- right.
left.
exact H30.
----------------------- apply (@H24).
------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
-------------------------intro H32.
apply (@euclidean__tactics.Col__nCol__False (b) (a) (c) (H2) H31).


---------------------- assert (* Cut *) (euclidean__axioms.neq c b) as H31.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (b) (c) H30).
----------------------- assert (* Cut *) (~(B = C)) as H32.
------------------------ intro H32.
assert (* Cut *) (euclidean__axioms.Col A B C) as H33.
------------------------- right.
right.
left.
exact H32.
------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H34.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H34.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H33).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H41.
------------------------------- exact H40.
------------------------------- destruct H41 as [H41 H42].
exact H35.
-------------------------- apply (@H24 H33).
------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H33.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H32).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS A U B) \/ ((B = U) \/ (euclidean__axioms.BetS A B U))) as H34.
-------------------------- apply (@lemma__ray1.lemma__ray1 (A) (B) (U) H8).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong B V b v) as H35.
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A U B) \/ ((B = U) \/ (euclidean__axioms.BetS A B U))) as H35.
---------------------------- exact H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A U B) \/ ((B = U) \/ (euclidean__axioms.BetS A B U))) as __TmpHyp.
----------------------------- exact H35.
----------------------------- assert (euclidean__axioms.BetS A U B \/ (B = U) \/ (euclidean__axioms.BetS A B U)) as H36.
------------------------------ exact __TmpHyp.
------------------------------ destruct H36 as [H36|H36].
------------------------------- assert (* Cut *) (euclidean__axioms.Cong A U A U) as H37.
-------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) U).
-------------------------------- assert (* Cut *) (euclidean__defs.Lt A U A B) as H38.
--------------------------------- exists U.
split.
---------------------------------- exact H36.
---------------------------------- exact H37.
--------------------------------- assert (* Cut *) (euclidean__defs.Lt A U a b) as H39.
---------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (U) (A) (B) (a) (b) (H38) H).
---------------------------------- assert (* Cut *) (exists (w: euclidean__axioms.Point), (euclidean__axioms.BetS a w b) /\ (euclidean__axioms.Cong a w A U)) as H40.
----------------------------------- exact H39.
----------------------------------- assert (exists w: euclidean__axioms.Point, ((euclidean__axioms.BetS a w b) /\ (euclidean__axioms.Cong a w A U))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [w H41].
assert (* AndElim *) ((euclidean__axioms.BetS a w b) /\ (euclidean__axioms.Cong a w A U)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__axioms.Cong a w a u) as H44.
-------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (w) (A) (U) (a) (u) (H43) H16).
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq a b) as H45.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq w b) /\ ((euclidean__axioms.neq a w) /\ (euclidean__axioms.neq a b))) as H45.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (w) (b) H42).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq w b) /\ ((euclidean__axioms.neq a w) /\ (euclidean__axioms.neq a b))) as H46.
----------------------------------------- exact H45.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq a w) /\ (euclidean__axioms.neq a b)) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
exact H49.
--------------------------------------- assert (* Cut *) (euclidean__defs.Out a b w) as H46.
---------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (b) (w)).
-----------------------------------------left.
exact H42.

----------------------------------------- exact H45.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a w a u) as H47.
----------------------------------------- exact H44.
----------------------------------------- assert (* Cut *) (w = u) as H48.
------------------------------------------ apply (@lemma__layoffunique.lemma__layoffunique (a) (b) (w) (u) (H46) (H12) H47).
------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS a u b) as H49.
------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun w0: euclidean__axioms.Point => (euclidean__axioms.BetS a w0 b) -> ((euclidean__axioms.Cong a w0 A U) -> ((euclidean__axioms.Cong a w0 a u) -> ((euclidean__defs.Out a b w0) -> ((euclidean__axioms.Cong a w0 a u) -> (euclidean__axioms.BetS a u b))))))) with (x := w).
--------------------------------------------intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
exact H49.

-------------------------------------------- exact H48.
-------------------------------------------- exact H42.
-------------------------------------------- exact H43.
-------------------------------------------- exact H44.
-------------------------------------------- exact H46.
-------------------------------------------- exact H47.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong U B u b) as H50.
-------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (U) (B) (a) (u) (b) (H16) (H) (H36) H49).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong V B v b) as H51.
--------------------------------------------- apply (@euclidean__axioms.axiom__5__line (A) (U) (B) (V) (a) (u) (b) (v) (H50) (H18) (H20) (H36) (H49) H16).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B V b v) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong B V v b) /\ (euclidean__axioms.Cong V B b v))) as H52.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (V) (B) (v) (b) H51).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong B V v b) /\ (euclidean__axioms.Cong V B b v))) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong B V v b) /\ (euclidean__axioms.Cong V B b v)) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
exact H53.
---------------------------------------------- exact H52.
------------------------------- assert (B = U \/ euclidean__axioms.BetS A B U) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37|H37].
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong B V u v) as H38.
---------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> (euclidean__axioms.Cong B0 V u v)))))))))) with (x := B).
-----------------------------------intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
exact H20.

----------------------------------- exact H37.
----------------------------------- exact H.
----------------------------------- exact H1.
----------------------------------- exact H8.
----------------------------------- exact H21.
----------------------------------- exact H24.
----------------------------------- exact H25.
----------------------------------- exact H32.
----------------------------------- exact H33.
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong a b A B) as H39.
----------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (A) (B) (b) H).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H40.
------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) B).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A B A U) as H41.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> (euclidean__axioms.Cong A B0 A U))))))))))))) with (x := B).
--------------------------------------intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
exact H51.

-------------------------------------- exact H37.
-------------------------------------- exact H.
-------------------------------------- exact H1.
-------------------------------------- exact H8.
-------------------------------------- exact H21.
-------------------------------------- exact H24.
-------------------------------------- exact H25.
-------------------------------------- exact H32.
-------------------------------------- exact H33.
-------------------------------------- exact H38.
-------------------------------------- exact H39.
-------------------------------------- exact H40.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a b A U) as H42.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> (euclidean__axioms.Cong a b A U)))))))))))))) with (x := B).
---------------------------------------intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
exact H51.

--------------------------------------- exact H37.
--------------------------------------- exact H.
--------------------------------------- exact H1.
--------------------------------------- exact H8.
--------------------------------------- exact H21.
--------------------------------------- exact H24.
--------------------------------------- exact H25.
--------------------------------------- exact H32.
--------------------------------------- exact H33.
--------------------------------------- exact H38.
--------------------------------------- exact H39.
--------------------------------------- exact H40.
--------------------------------------- exact H41.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a b a u) as H43.
--------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (b) (A) (U) (a) (u) (H42) H16).
--------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS a u b) \/ ((b = u) \/ (euclidean__axioms.BetS a b u))) as H44.
---------------------------------------- apply (@lemma__ray1.lemma__ray1 (a) (b) (u) H12).
---------------------------------------- assert (* Cut *) (b = u) as H45.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS a u b) \/ ((b = u) \/ (euclidean__axioms.BetS a b u))) as H45.
------------------------------------------ exact H44.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS a u b) \/ ((b = u) \/ (euclidean__axioms.BetS a b u))) as __TmpHyp0.
------------------------------------------- exact H45.
------------------------------------------- assert (euclidean__axioms.BetS a u b \/ (b = u) \/ (euclidean__axioms.BetS a b u)) as H46.
-------------------------------------------- exact __TmpHyp0.
-------------------------------------------- destruct H46 as [H46|H46].
--------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq b u)) as H47.
---------------------------------------------- intro H47.
assert (* Cut *) (~(euclidean__axioms.Cong a u a b)) as H48.
----------------------------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (a) (u) (b) H46).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a u a b) as H49.
------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (a) (b) (u) H43).
------------------------------------------------ apply (@H24).
-------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
--------------------------------------------------intro H50.
apply (@H48 H49).


---------------------------------------------- apply (@euclidean__tactics.NNPP (b = u)).
-----------------------------------------------intro H48.
assert (* AndElim *) ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))))))) as H49.
------------------------------------------------ exact H2.
------------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H51.
------------------------------------------------- exact H21.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c)))))) as H53.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H55.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))))) as H57.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H59.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c)))) as H61.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H63.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))) as H65.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H67.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* Cut *) (False) as H69.
---------------------------------------------------------- apply (@H47 H48).
---------------------------------------------------------- assert False.
-----------------------------------------------------------exact H69.
----------------------------------------------------------- contradiction.

--------------------------------------------- assert (b = u \/ euclidean__axioms.BetS a b u) as H47.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H47 as [H47|H47].
----------------------------------------------- exact H47.
----------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq b u)) as H48.
------------------------------------------------ intro H48.
assert (* Cut *) (~(euclidean__axioms.Cong a b a u)) as H49.
------------------------------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (a) (b) (u) H47).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a b A B) as H50.
-------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> (euclidean__axioms.Cong a b A B0)))))))))))))) with (x := B).
---------------------------------------------------intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
exact H42.

--------------------------------------------------- exact H37.
--------------------------------------------------- exact H.
--------------------------------------------------- exact H1.
--------------------------------------------------- exact H8.
--------------------------------------------------- exact H21.
--------------------------------------------------- exact H24.
--------------------------------------------------- exact H25.
--------------------------------------------------- exact H32.
--------------------------------------------------- exact H33.
--------------------------------------------------- exact H38.
--------------------------------------------------- exact H39.
--------------------------------------------------- exact H40.
--------------------------------------------------- exact H41.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H51.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> ((euclidean__axioms.Cong a b A B0) -> (euclidean__axioms.Cong A B0 A B0))))))))))))))) with (x := B).
----------------------------------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
exact H61.

---------------------------------------------------- exact H37.
---------------------------------------------------- exact H.
---------------------------------------------------- exact H1.
---------------------------------------------------- exact H8.
---------------------------------------------------- exact H21.
---------------------------------------------------- exact H24.
---------------------------------------------------- exact H25.
---------------------------------------------------- exact H32.
---------------------------------------------------- exact H33.
---------------------------------------------------- exact H38.
---------------------------------------------------- exact H39.
---------------------------------------------------- exact H40.
---------------------------------------------------- exact H41.
---------------------------------------------------- exact H50.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A U) as H52.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> (euclidean__axioms.Cong A B0 A U)))))))))))))))) with (x := B).
-----------------------------------------------------intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
exact H65.

----------------------------------------------------- exact H37.
----------------------------------------------------- exact H.
----------------------------------------------------- exact H1.
----------------------------------------------------- exact H8.
----------------------------------------------------- exact H21.
----------------------------------------------------- exact H24.
----------------------------------------------------- exact H25.
----------------------------------------------------- exact H32.
----------------------------------------------------- exact H33.
----------------------------------------------------- exact H38.
----------------------------------------------------- exact H39.
----------------------------------------------------- exact H40.
----------------------------------------------------- exact H41.
----------------------------------------------------- exact H50.
----------------------------------------------------- exact H51.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B a u) as H53.
----------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> (euclidean__axioms.Cong A B0 a u))))))))))))))))) with (x := B).
------------------------------------------------------intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
exact H16.

------------------------------------------------------ exact H37.
------------------------------------------------------ exact H.
------------------------------------------------------ exact H1.
------------------------------------------------------ exact H8.
------------------------------------------------------ exact H21.
------------------------------------------------------ exact H24.
------------------------------------------------------ exact H25.
------------------------------------------------------ exact H32.
------------------------------------------------------ exact H33.
------------------------------------------------------ exact H38.
------------------------------------------------------ exact H39.
------------------------------------------------------ exact H40.
------------------------------------------------------ exact H41.
------------------------------------------------------ exact H50.
------------------------------------------------------ exact H51.
------------------------------------------------------ exact H52.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a b a u) as H54.
------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__defs.CongA B0 A C b a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> ((euclidean__axioms.Cong a b A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> ((euclidean__axioms.Cong A B0 a u) -> (euclidean__axioms.Cong a b a u)))))))))))))))))) with (x := B).
-------------------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
exact H43.

------------------------------------------------------- exact H37.
------------------------------------------------------- exact H.
------------------------------------------------------- exact H1.
------------------------------------------------------- exact H8.
------------------------------------------------------- exact H21.
------------------------------------------------------- exact H24.
------------------------------------------------------- exact H25.
------------------------------------------------------- exact H32.
------------------------------------------------------- exact H33.
------------------------------------------------------- exact H38.
------------------------------------------------------- exact H39.
------------------------------------------------------- exact H40.
------------------------------------------------------- exact H41.
------------------------------------------------------- exact H50.
------------------------------------------------------- exact H51.
------------------------------------------------------- exact H52.
------------------------------------------------------- exact H53.
------------------------------------------------------ apply (@H24).
-------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
--------------------------------------------------------intro H55.
apply (@H49 H54).


------------------------------------------------ apply (@euclidean__tactics.NNPP (b = u)).
-------------------------------------------------intro H49.
assert (* AndElim *) ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))))))) as H50.
-------------------------------------------------- exact H2.
-------------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H52.
--------------------------------------------------- exact H21.
--------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c)))))) as H54.
---------------------------------------------------- exact H51.
---------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H56.
----------------------------------------------------- exact H53.
----------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq a c) /\ ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))))) as H58.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H60.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS b a c)) /\ ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c)))) as H62.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H64.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((~(euclidean__axioms.BetS b c a)) /\ (~(euclidean__axioms.BetS a b c))) as H66.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H68.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* Cut *) (False) as H70.
------------------------------------------------------------ apply (@H48 H49).
------------------------------------------------------------ assert False.
-------------------------------------------------------------exact H70.
------------------------------------------------------------- contradiction.

----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B V b v) as H46.
------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point u (fun b0: euclidean__axioms.Point => (euclidean__axioms.Cong A B a b0) -> ((euclidean__defs.CongA B A C b0 a c) -> ((euclidean__axioms.nCol b0 a c) -> ((euclidean__defs.Out a b0 u) -> ((euclidean__axioms.neq a b0) -> ((euclidean__axioms.neq b0 a) -> ((~(b0 = c)) -> ((euclidean__axioms.neq c b0) -> ((euclidean__axioms.Cong a b0 A B) -> ((euclidean__axioms.Cong a b0 A U) -> ((euclidean__axioms.Cong a b0 a u) -> (((euclidean__axioms.BetS a u b0) \/ ((b0 = u) \/ (euclidean__axioms.BetS a b0 u))) -> (euclidean__axioms.Cong B V b0 v)))))))))))))) with (x := b).
-------------------------------------------intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
apply (@eq__ind__r euclidean__axioms.Point U (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a u) -> ((euclidean__defs.CongA B0 A C u a c) -> ((euclidean__defs.Out A B0 U) -> ((euclidean__axioms.nCol B0 A C) -> ((~(euclidean__axioms.Col A B0 C)) -> ((~(A = B0)) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Cong B0 V u v) -> ((euclidean__axioms.Cong a u A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A U) -> (euclidean__axioms.Cong B0 V u v)))))))))))))) with (x := B).
--------------------------------------------intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
exact H66.

-------------------------------------------- exact H37.
-------------------------------------------- exact H46.
-------------------------------------------- exact H47.
-------------------------------------------- exact H8.
-------------------------------------------- exact H21.
-------------------------------------------- exact H24.
-------------------------------------------- exact H25.
-------------------------------------------- exact H32.
-------------------------------------------- exact H33.
-------------------------------------------- exact H38.
-------------------------------------------- exact H54.
-------------------------------------------- exact H40.
-------------------------------------------- exact H41.

------------------------------------------- exact H45.
------------------------------------------- exact H.
------------------------------------------- exact H1.
------------------------------------------- exact H2.
------------------------------------------- exact H12.
------------------------------------------- exact H22.
------------------------------------------- exact H23.
------------------------------------------- exact H30.
------------------------------------------- exact H31.
------------------------------------------- exact H39.
------------------------------------------- exact H42.
------------------------------------------- exact H43.
------------------------------------------- exact H44.
------------------------------------------ exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H38.
---------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt A B A U) as H39.
----------------------------------- exists B.
split.
------------------------------------ exact H37.
------------------------------------ exact H38.
----------------------------------- assert (* Cut *) (euclidean__defs.Lt A B a u) as H40.
------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (A) (U) (a) (u) (H39) H16).
------------------------------------ assert (* Cut *) (exists (f: euclidean__axioms.Point), (euclidean__axioms.BetS a f u) /\ (euclidean__axioms.Cong a f A B)) as H41.
------------------------------------- exact H40.
------------------------------------- assert (exists f: euclidean__axioms.Point, ((euclidean__axioms.BetS a f u) /\ (euclidean__axioms.Cong a f A B))) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [f H42].
assert (* AndElim *) ((euclidean__axioms.BetS a f u) /\ (euclidean__axioms.Cong a f A B)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) (euclidean__axioms.neq a u) as H45.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq f u) /\ ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a u))) as H45.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (f) (u) H43).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq f u) /\ ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a u))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a u)) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
exact H49.
---------------------------------------- assert (* Cut *) (euclidean__defs.Out a u f) as H46.
----------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (u) (f)).
------------------------------------------left.
exact H43.

------------------------------------------ exact H45.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out a u b) as H47.
------------------------------------------ apply (@lemma__ray5.lemma__ray5 (a) (b) (u) H12).
------------------------------------------ assert (* Cut *) (euclidean__defs.Out a b f) as H48.
------------------------------------------- apply (@lemma__ray3.lemma__ray3 (a) (u) (b) (f) (H47) H46).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a f a b) as H49.
-------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (f) (A) (B) (a) (b) (H44) H).
-------------------------------------------- assert (* Cut *) (f = b) as H50.
--------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (a) (u) (f) (b) (H46) (H47) H49).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a b u) as H51.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point b (fun f0: euclidean__axioms.Point => (euclidean__axioms.BetS a f0 u) -> ((euclidean__axioms.Cong a f0 A B) -> ((euclidean__defs.Out a u f0) -> ((euclidean__defs.Out a b f0) -> ((euclidean__axioms.Cong a f0 a b) -> (euclidean__axioms.BetS a b u))))))) with (x := f).
-----------------------------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
exact H51.

----------------------------------------------- exact H50.
----------------------------------------------- exact H43.
----------------------------------------------- exact H44.
----------------------------------------------- exact H46.
----------------------------------------------- exact H48.
----------------------------------------------- exact H49.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B U b u) as H52.
----------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (B) (U) (a) (b) (u) (H) (H16) (H37) H51).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a b u) as H53.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point b (fun f0: euclidean__axioms.Point => (euclidean__axioms.BetS a f0 u) -> ((euclidean__axioms.Cong a f0 A B) -> ((euclidean__defs.Out a u f0) -> ((euclidean__defs.Out a b f0) -> ((euclidean__axioms.Cong a f0 a b) -> (euclidean__axioms.BetS a b u))))))) with (x := f).
-------------------------------------------------intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
exact H51.

------------------------------------------------- exact H50.
------------------------------------------------- exact H43.
------------------------------------------------- exact H44.
------------------------------------------------- exact H46.
------------------------------------------------- exact H48.
------------------------------------------------- exact H49.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B U b u) as H54.
------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point b (fun f0: euclidean__axioms.Point => (euclidean__axioms.BetS a f0 u) -> ((euclidean__axioms.Cong a f0 A B) -> ((euclidean__defs.Out a u f0) -> ((euclidean__defs.Out a b f0) -> ((euclidean__axioms.Cong a f0 a b) -> (euclidean__axioms.Cong B U b u))))))) with (x := f).
--------------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H52.

-------------------------------------------------- exact H50.
-------------------------------------------------- exact H43.
-------------------------------------------------- exact H44.
-------------------------------------------------- exact H46.
-------------------------------------------------- exact H48.
-------------------------------------------------- exact H49.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B V b v) as H55.
-------------------------------------------------- apply (@lemma__interior5.lemma__interior5 (A) (B) (U) (V) (a) (b) (u) (v) (H37) (H53) (H) (H54) (H18) H20).
-------------------------------------------------- exact H55.
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A V C) \/ ((C = V) \/ (euclidean__axioms.BetS A C V))) as H36.
---------------------------- apply (@lemma__ray1.lemma__ray1 (A) (C) (V) H10).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H37.
----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A V C) \/ ((C = V) \/ (euclidean__axioms.BetS A C V))) as H37.
------------------------------ exact H36.
------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A V C) \/ ((C = V) \/ (euclidean__axioms.BetS A C V))) as __TmpHyp.
------------------------------- exact H37.
------------------------------- assert (euclidean__axioms.BetS A V C \/ (C = V) \/ (euclidean__axioms.BetS A C V)) as H38.
-------------------------------- exact __TmpHyp.
-------------------------------- destruct H38 as [H38|H38].
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A V A V) as H39.
---------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) V).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt A V A C) as H40.
----------------------------------- exists V.
split.
------------------------------------ exact H38.
------------------------------------ exact H39.
----------------------------------- assert (* Cut *) (euclidean__defs.Lt A V a c) as H41.
------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (V) (A) (C) (a) (c) (H40) H0).
------------------------------------ assert (* Cut *) (exists (g: euclidean__axioms.Point), (euclidean__axioms.BetS a g c) /\ (euclidean__axioms.Cong a g A V)) as H42.
------------------------------------- exact H41.
------------------------------------- assert (exists g: euclidean__axioms.Point, ((euclidean__axioms.BetS a g c) /\ (euclidean__axioms.Cong a g A V))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [g H43].
assert (* AndElim *) ((euclidean__axioms.BetS a g c) /\ (euclidean__axioms.Cong a g A V)) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) (euclidean__axioms.neq a g) as H46.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq g c) /\ ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a c))) as H46.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (g) (c) H44).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq g c) /\ ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a c))) as H47.
------------------------------------------ exact H46.
------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a c)) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
exact H49.
---------------------------------------- assert (* Cut *) (euclidean__defs.Out a g c) as H47.
----------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (g) (c)).
------------------------------------------right.
right.
exact H44.

------------------------------------------ exact H46.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out a c g) as H48.
------------------------------------------ apply (@lemma__ray5.lemma__ray5 (a) (g) (c) H47).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong a g a v) as H49.
------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (g) (A) (V) (a) (v) (H45) H18).
------------------------------------------- assert (* Cut *) (g = v) as H50.
-------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (a) (c) (g) (v) (H48) (H14) H49).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a v c) as H51.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point v (fun g0: euclidean__axioms.Point => (euclidean__axioms.BetS a g0 c) -> ((euclidean__axioms.Cong a g0 A V) -> ((euclidean__axioms.neq a g0) -> ((euclidean__defs.Out a g0 c) -> ((euclidean__defs.Out a c g0) -> ((euclidean__axioms.Cong a g0 a v) -> (euclidean__axioms.BetS a v c)))))))) with (x := g).
----------------------------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H51.

---------------------------------------------- exact H50.
---------------------------------------------- exact H44.
---------------------------------------------- exact H45.
---------------------------------------------- exact H46.
---------------------------------------------- exact H47.
---------------------------------------------- exact H48.
---------------------------------------------- exact H49.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong V C v c) as H52.
---------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (V) (C) (a) (v) (c) (H18) (H0) (H38) H51).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong V B v b) as H53.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong V B v b) /\ ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b))) as H53.
------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (B) (V) (b) (v) H35).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong V B v b) /\ ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b)) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
exact H54.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H54.
------------------------------------------------ apply (@euclidean__axioms.axiom__5__line (A) (V) (C) (B) (a) (v) (c) (b) (H52) (H) (H53) (H38) (H51) H18).
------------------------------------------------ exact H54.
--------------------------------- assert (C = V \/ euclidean__axioms.BetS A C V) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39|H39].
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C a v) as H40.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point V (fun C0: euclidean__axioms.Point => (euclidean__axioms.Cong A C0 a c) -> ((euclidean__defs.CongA B A C0 b a c) -> ((euclidean__defs.Out A C0 V) -> ((euclidean__axioms.nCol B A C0) -> ((~(euclidean__axioms.Col A B C0)) -> ((~(A = C0)) -> ((euclidean__axioms.neq C0 A) -> ((~(B = C0)) -> ((euclidean__axioms.neq C0 B) -> (euclidean__axioms.Cong A C0 a v))))))))))) with (x := C).
-------------------------------------intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
exact H18.

------------------------------------- exact H39.
------------------------------------- exact H0.
------------------------------------- exact H1.
------------------------------------- exact H10.
------------------------------------- exact H21.
------------------------------------- exact H24.
------------------------------------- exact H26.
------------------------------------- exact H27.
------------------------------------- exact H32.
------------------------------------- exact H33.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong a c A C) as H41.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (A) (C) (c) H0).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a c a v) as H42.
-------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (c) (A) (C) (a) (v) (H41) H40).
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq a c) as H43.
--------------------------------------- apply (@eq__ind__r euclidean__axioms.Point V (fun C0: euclidean__axioms.Point => (euclidean__axioms.Cong A C0 a c) -> ((euclidean__defs.CongA B A C0 b a c) -> ((euclidean__defs.Out A C0 V) -> ((euclidean__axioms.nCol B A C0) -> ((~(euclidean__axioms.Col A B C0)) -> ((~(A = C0)) -> ((euclidean__axioms.neq C0 A) -> ((~(B = C0)) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Cong A C0 a v) -> ((euclidean__axioms.Cong a c A C0) -> (euclidean__axioms.neq a c))))))))))))) with (x := C).
----------------------------------------intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
exact H28.

---------------------------------------- exact H39.
---------------------------------------- exact H0.
---------------------------------------- exact H1.
---------------------------------------- exact H10.
---------------------------------------- exact H21.
---------------------------------------- exact H24.
---------------------------------------- exact H26.
---------------------------------------- exact H27.
---------------------------------------- exact H32.
---------------------------------------- exact H33.
---------------------------------------- exact H40.
---------------------------------------- exact H41.
--------------------------------------- assert (* Cut *) (c = c) as H44.
---------------------------------------- apply (@logic.eq__refl (Point) c).
---------------------------------------- assert (* Cut *) (euclidean__defs.Out a c c) as H45.
----------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (c) (c)).
------------------------------------------right.
left.
exact H44.

------------------------------------------ exact H43.
----------------------------------------- assert (* Cut *) (c = v) as H46.
------------------------------------------ apply (@lemma__layoffunique.lemma__layoffunique (a) (c) (c) (v) (H45) (H14) H42).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B C b v) as H47.
------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point v (fun c0: euclidean__axioms.Point => (euclidean__axioms.Cong A C a c0) -> ((euclidean__defs.CongA B A C b a c0) -> ((euclidean__axioms.nCol b a c0) -> ((euclidean__defs.Out a c0 v) -> ((~(a = c0)) -> ((euclidean__axioms.neq c0 a) -> ((~(b = c0)) -> ((euclidean__axioms.neq c0 b) -> ((euclidean__axioms.Cong a c0 A C) -> ((euclidean__axioms.Cong a c0 a v) -> ((euclidean__axioms.neq a c0) -> ((c0 = c0) -> ((euclidean__defs.Out a c0 c0) -> (euclidean__axioms.Cong B C b v))))))))))))))) with (x := c).
--------------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
apply (@eq__ind__r euclidean__axioms.Point V (fun C0: euclidean__axioms.Point => (euclidean__defs.CongA B A C0 b a v) -> ((euclidean__axioms.Cong A C0 a v) -> ((euclidean__defs.Out A C0 V) -> ((euclidean__axioms.nCol B A C0) -> ((~(euclidean__axioms.Col A B C0)) -> ((~(A = C0)) -> ((euclidean__axioms.neq C0 A) -> ((~(B = C0)) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Cong A C0 a v) -> ((euclidean__axioms.Cong a v A C0) -> (euclidean__axioms.Cong B C0 b v))))))))))))) with (x := C).
---------------------------------------------intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
exact H35.

--------------------------------------------- exact H39.
--------------------------------------------- exact H48.
--------------------------------------------- exact H47.
--------------------------------------------- exact H10.
--------------------------------------------- exact H21.
--------------------------------------------- exact H24.
--------------------------------------------- exact H26.
--------------------------------------------- exact H27.
--------------------------------------------- exact H32.
--------------------------------------------- exact H33.
--------------------------------------------- exact H40.
--------------------------------------------- exact H55.

-------------------------------------------- exact H46.
-------------------------------------------- exact H0.
-------------------------------------------- exact H1.
-------------------------------------------- exact H2.
-------------------------------------------- exact H14.
-------------------------------------------- exact H28.
-------------------------------------------- exact H29.
-------------------------------------------- exact H30.
-------------------------------------------- exact H31.
-------------------------------------------- exact H41.
-------------------------------------------- exact H42.
-------------------------------------------- exact H43.
-------------------------------------------- exact H44.
-------------------------------------------- exact H45.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H48.
-------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point v (fun c0: euclidean__axioms.Point => (euclidean__axioms.Cong A C a c0) -> ((euclidean__defs.CongA B A C b a c0) -> ((euclidean__axioms.nCol b a c0) -> ((euclidean__defs.Out a c0 v) -> ((~(a = c0)) -> ((euclidean__axioms.neq c0 a) -> ((~(b = c0)) -> ((euclidean__axioms.neq c0 b) -> ((euclidean__axioms.Cong a c0 A C) -> ((euclidean__axioms.Cong a c0 a v) -> ((euclidean__axioms.neq a c0) -> ((c0 = c0) -> ((euclidean__defs.Out a c0 c0) -> (euclidean__axioms.Cong B C b c0))))))))))))))) with (x := c).
---------------------------------------------intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
apply (@eq__ind__r euclidean__axioms.Point V (fun C0: euclidean__axioms.Point => (euclidean__defs.CongA B A C0 b a v) -> ((euclidean__axioms.Cong A C0 a v) -> ((euclidean__defs.Out A C0 V) -> ((euclidean__axioms.nCol B A C0) -> ((~(euclidean__axioms.Col A B C0)) -> ((~(A = C0)) -> ((euclidean__axioms.neq C0 A) -> ((~(B = C0)) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Cong A C0 a v) -> ((euclidean__axioms.Cong a v A C0) -> ((euclidean__axioms.Cong B C0 b v) -> (euclidean__axioms.Cong B C0 b v)))))))))))))) with (x := C).
----------------------------------------------intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
exact H72.

---------------------------------------------- exact H39.
---------------------------------------------- exact H49.
---------------------------------------------- exact H48.
---------------------------------------------- exact H10.
---------------------------------------------- exact H21.
---------------------------------------------- exact H24.
---------------------------------------------- exact H26.
---------------------------------------------- exact H27.
---------------------------------------------- exact H32.
---------------------------------------------- exact H33.
---------------------------------------------- exact H40.
---------------------------------------------- exact H56.
---------------------------------------------- exact H47.

--------------------------------------------- exact H46.
--------------------------------------------- exact H0.
--------------------------------------------- exact H1.
--------------------------------------------- exact H2.
--------------------------------------------- exact H14.
--------------------------------------------- exact H28.
--------------------------------------------- exact H29.
--------------------------------------------- exact H30.
--------------------------------------------- exact H31.
--------------------------------------------- exact H41.
--------------------------------------------- exact H42.
--------------------------------------------- exact H43.
--------------------------------------------- exact H44.
--------------------------------------------- exact H45.
-------------------------------------------- exact H48.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H40.
------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) C).
------------------------------------ assert (* Cut *) (euclidean__defs.Lt A C A V) as H41.
------------------------------------- exists C.
split.
-------------------------------------- exact H39.
-------------------------------------- exact H40.
------------------------------------- assert (* Cut *) (euclidean__defs.Lt A C a v) as H42.
-------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (C) (A) (V) (a) (v) (H41) H18).
-------------------------------------- assert (* Cut *) (exists (g: euclidean__axioms.Point), (euclidean__axioms.BetS a g v) /\ (euclidean__axioms.Cong a g A C)) as H43.
--------------------------------------- exact H42.
--------------------------------------- assert (exists g: euclidean__axioms.Point, ((euclidean__axioms.BetS a g v) /\ (euclidean__axioms.Cong a g A C))) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [g H44].
assert (* AndElim *) ((euclidean__axioms.BetS a g v) /\ (euclidean__axioms.Cong a g A C)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
assert (* Cut *) (euclidean__axioms.neq a g) as H47.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq g v) /\ ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a v))) as H47.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (g) (v) H45).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq g v) /\ ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a v))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq a g) /\ (euclidean__axioms.neq a v)) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
exact H50.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out a g v) as H48.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (g) (v)).
--------------------------------------------right.
right.
exact H45.

-------------------------------------------- exact H47.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out a v g) as H49.
-------------------------------------------- apply (@lemma__ray5.lemma__ray5 (a) (g) (v) H48).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a g a c) as H50.
--------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (g) (A) (C) (a) (c) (H46) H0).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a c a g) as H51.
---------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (a) (g) (c) H50).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out a v c) as H52.
----------------------------------------------- apply (@lemma__ray5.lemma__ray5 (a) (c) (v) H14).
----------------------------------------------- assert (* Cut *) (c = g) as H53.
------------------------------------------------ apply (@lemma__layoffunique.lemma__layoffunique (a) (v) (c) (g) (H52) (H49) H51).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS a c v) as H54.
------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point g (fun c0: euclidean__axioms.Point => (euclidean__axioms.Cong A C a c0) -> ((euclidean__defs.CongA B A C b a c0) -> ((euclidean__axioms.nCol b a c0) -> ((euclidean__defs.Out a c0 v) -> ((~(a = c0)) -> ((euclidean__axioms.neq c0 a) -> ((~(b = c0)) -> ((euclidean__axioms.neq c0 b) -> ((euclidean__axioms.Cong a g a c0) -> ((euclidean__axioms.Cong a c0 a g) -> ((euclidean__defs.Out a v c0) -> (euclidean__axioms.BetS a c0 v))))))))))))) with (x := c).
--------------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
exact H45.

-------------------------------------------------- exact H53.
-------------------------------------------------- exact H0.
-------------------------------------------------- exact H1.
-------------------------------------------------- exact H2.
-------------------------------------------------- exact H14.
-------------------------------------------------- exact H28.
-------------------------------------------------- exact H29.
-------------------------------------------------- exact H30.
-------------------------------------------------- exact H31.
-------------------------------------------------- exact H50.
-------------------------------------------------- exact H51.
-------------------------------------------------- exact H52.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C V c v) as H55.
-------------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (C) (V) (a) (c) (v) (H0) (H18) (H39) H54).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong V B v b) as H56.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong V B v b) /\ ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b))) as H56.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (V) (b) (v) H35).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong V B v b) /\ ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b))) as H57.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong V B b v) /\ (euclidean__axioms.Cong B V v b)) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [H59 H60].
exact H57.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B c b) as H57.
---------------------------------------------------- apply (@lemma__interior5.lemma__interior5 (A) (C) (V) (B) (a) (c) (v) (b) (H39) (H54) (H0) (H55) (H) H56).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H58.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B C b c) /\ ((euclidean__axioms.Cong B C c b) /\ (euclidean__axioms.Cong C B b c))) as H58.
------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (C) (B) (c) (b) H57).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B C b c) /\ ((euclidean__axioms.Cong B C c b) /\ (euclidean__axioms.Cong C B b c))) as H59.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong B C c b) /\ (euclidean__axioms.Cong C B b c)) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [H61 H62].
exact H59.
----------------------------------------------------- exact H58.
----------------------------- assert (* Cut *) (A = A) as H38.
------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------ assert (* Cut *) (C = C) as H39.
------------------------------- apply (@logic.eq__refl (Point) C).
------------------------------- assert (* Cut *) (a = a) as H40.
-------------------------------- apply (@logic.eq__refl (Point) a).
-------------------------------- assert (* Cut *) (c = c) as H41.
--------------------------------- apply (@logic.eq__refl (Point) c).
--------------------------------- assert (* Cut *) (B = B) as H42.
---------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------- assert (* Cut *) (b = b) as H43.
----------------------------------- apply (@logic.eq__refl (Point) b).
----------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H44.
------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H25).
------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H45.
------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
--------------------------------------right.
left.
exact H38.

-------------------------------------- exact H44.
------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H46.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
---------------------------------------right.
left.
exact H39.

--------------------------------------- exact H32.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out b a a) as H47.
--------------------------------------- apply (@lemma__ray4.lemma__ray4 (b) (a) (a)).
----------------------------------------right.
left.
exact H40.

---------------------------------------- exact H23.
--------------------------------------- assert (* Cut *) (euclidean__defs.Out b c c) as H48.
---------------------------------------- apply (@lemma__ray4.lemma__ray4 (b) (c) (c)).
-----------------------------------------right.
left.
exact H41.

----------------------------------------- exact H30.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A b a) as H49.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A b a) /\ ((euclidean__axioms.Cong B A a b) /\ (euclidean__axioms.Cong A B b a))) as H49.
------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (a) (b) H).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A b a) /\ ((euclidean__axioms.Cong B A a b) /\ (euclidean__axioms.Cong A B b a))) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Cong B A a b) /\ (euclidean__axioms.Cong A B b a)) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
exact H50.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C a b c) as H50.
------------------------------------------ exists A.
exists C.
exists a.
exists c.
split.
------------------------------------------- exact H45.
------------------------------------------- split.
-------------------------------------------- exact H46.
-------------------------------------------- split.
--------------------------------------------- exact H47.
--------------------------------------------- split.
---------------------------------------------- exact H48.
---------------------------------------------- split.
----------------------------------------------- exact H49.
----------------------------------------------- split.
------------------------------------------------ exact H37.
------------------------------------------------ split.
------------------------------------------------- exact H0.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H24).
------------------------------------------ assert (* Cut *) (euclidean__defs.Out C A A) as H51.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
--------------------------------------------right.
left.
exact H38.

-------------------------------------------- exact H27.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H52.
-------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
---------------------------------------------right.
left.
exact H42.

--------------------------------------------- exact H33.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Out c a a) as H53.
--------------------------------------------- apply (@lemma__ray4.lemma__ray4 (c) (a) (a)).
----------------------------------------------right.
left.
exact H40.

---------------------------------------------- exact H29.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Out c b b) as H54.
---------------------------------------------- apply (@lemma__ray4.lemma__ray4 (c) (b) (b)).
-----------------------------------------------right.
left.
exact H43.

----------------------------------------------- exact H31.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A c a) as H55.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C A c a) /\ ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a))) as H55.
------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (a) (c) H0).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C A c a) /\ ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a))) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a)) as H58.
-------------------------------------------------- exact H57.
-------------------------------------------------- destruct H58 as [H58 H59].
exact H56.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B c b) as H56.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong C B c b) /\ ((euclidean__axioms.Cong C B b c) /\ (euclidean__axioms.Cong B C c b))) as H56.
------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (b) (c) H37).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B c b) /\ ((euclidean__axioms.Cong C B b c) /\ (euclidean__axioms.Cong B C c b))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong C B b c) /\ (euclidean__axioms.Cong B C c b)) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H57.
------------------------------------------------- intro H57.
assert (* Cut *) (euclidean__axioms.Col A B C) as H58.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H58.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H57).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
-------------------------------------------------- apply (@H24 H58).
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C B a c b) as H58.
-------------------------------------------------- exists A.
exists B.
exists a.
exists b.
split.
--------------------------------------------------- exact H51.
--------------------------------------------------- split.
---------------------------------------------------- exact H52.
---------------------------------------------------- split.
----------------------------------------------------- exact H53.
----------------------------------------------------- split.
------------------------------------------------------ exact H54.
------------------------------------------------------ split.
------------------------------------------------------- exact H55.
------------------------------------------------------- split.
-------------------------------------------------------- exact H56.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H.
--------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H57).
-------------------------------------------------- split.
--------------------------------------------------- exact H37.
--------------------------------------------------- split.
---------------------------------------------------- exact H50.
---------------------------------------------------- exact H58.
Qed.
