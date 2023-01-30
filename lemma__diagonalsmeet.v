Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__diagonalsmeet : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0.
- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
split.
----- exact H1.
----- exact H2.
- assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H1.
-- assert (* AndElim *) ((exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
exact H1.
-- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H2.
--- exact H1.
--- destruct H2 as [a H2].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H3.
---- exact H2.
---- destruct H3 as [b H3].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [c H4].
assert (exists d: euclidean__axioms.Point, (exists (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [d H5].
assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H6.
------- exact H5.
------- destruct H6 as [m H6].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H27.
------------------ exact H0.
------------------ destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__defs.Par C D A B) as H29.
------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (D) H27).
------------------- assert (* Cut *) (euclidean__defs.TP C D A B) as H30.
-------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (C) (D) (A) (B) H29).
-------------------- assert (* Cut *) (euclidean__defs.OS A B C D) as H31.
--------------------- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D)))) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D)) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
exact H36.
--------------------- assert (* Cut *) (D = D) as H32.
---------------------- apply (@logic.eq__refl (Point) D).
---------------------- assert (* Cut *) (euclidean__axioms.Col D C D) as H33.
----------------------- right.
left.
exact H32.
----------------------- assert (* Cut *) (~(A = D)) as H34.
------------------------ intro H34.
assert (* Cut *) (euclidean__axioms.Col D C A) as H35.
------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B a) -> ((euclidean__axioms.Col A0 B b) -> ((~(euclidean__defs.Meet A0 B C D)) -> ((euclidean__defs.Par C D A0 B) -> ((euclidean__defs.TP C D A0 B) -> ((euclidean__defs.OS A0 B C D) -> (euclidean__axioms.Col D C A0)))))))))))) with (x := A).
--------------------------intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
exact H33.

-------------------------- exact H34.
-------------------------- exact H.
-------------------------- exact H27.
-------------------------- exact H28.
-------------------------- exact H7.
-------------------------- exact H11.
-------------------------- exact H13.
-------------------------- exact H23.
-------------------------- exact H29.
-------------------------- exact H30.
-------------------------- exact H31.
------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H36.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H36.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (A) H35).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)))) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
exact H37.
-------------------------- assert (* Cut *) (A = A) as H37.
--------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B a) -> ((euclidean__axioms.Col A0 B b) -> ((~(euclidean__defs.Meet A0 B C D)) -> ((euclidean__defs.Par C D A0 B) -> ((euclidean__defs.TP C D A0 B) -> ((euclidean__defs.OS A0 B C D) -> ((euclidean__axioms.Col D C A0) -> ((euclidean__axioms.Col C D A0) -> (A0 = A0)))))))))))))) with (x := A).
----------------------------intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
exact H32.

---------------------------- exact H34.
---------------------------- exact H.
---------------------------- exact H27.
---------------------------- exact H28.
---------------------------- exact H7.
---------------------------- exact H11.
---------------------------- exact H13.
---------------------------- exact H23.
---------------------------- exact H29.
---------------------------- exact H30.
---------------------------- exact H31.
---------------------------- exact H35.
---------------------------- exact H36.
--------------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H38.
---------------------------- right.
left.
exact H37.
---------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H39.
----------------------------- exists A.
split.
------------------------------ exact H7.
------------------------------ split.
------------------------------- exact H9.
------------------------------- split.
-------------------------------- exact H38.
-------------------------------- exact H36.
----------------------------- apply (@H23 H39).
------------------------ assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A D E) /\ (euclidean__axioms.Cong D E A D)) as H35.
------------------------- apply (@lemma__extension.lemma__extension (A) (D) (A) (D) (H34) H34).
------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A D E) /\ (euclidean__axioms.Cong D E A D))) as H36.
-------------------------- exact H35.
-------------------------- destruct H36 as [E H36].
assert (* AndElim *) ((euclidean__axioms.BetS A D E) /\ (euclidean__axioms.Cong D E A D)) as H37.
--------------------------- exact H36.
--------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (~(euclidean__axioms.Col D C A)) as H39.
---------------------------- intro H39.
assert (* Cut *) (A = A) as H40.
----------------------------- apply (@logic.eq__refl (Point) A).
----------------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H41.
------------------------------ right.
left.
exact H40.
------------------------------ assert (* Cut *) (euclidean__axioms.Col C D A) as H42.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H42.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (A) H39).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
exact H43.
------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H43.
-------------------------------- exists A.
split.
--------------------------------- exact H7.
--------------------------------- split.
---------------------------------- exact H9.
---------------------------------- split.
----------------------------------- exact H41.
----------------------------------- exact H42.
-------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H44.
--------------------------------- exact H23.
--------------------------------- apply (@H23 H43).
---------------------------- assert (* Cut *) (euclidean__axioms.TS A D C E) as H40.
----------------------------- exists D.
split.
------------------------------ exact H37.
------------------------------ split.
------------------------------- exact H33.
------------------------------- apply (@euclidean__tactics.nCol__notCol (D) (C) (A) H39).
----------------------------- assert (* Cut *) (euclidean__defs.OS B A D C) as H41.
------------------------------ assert (* Cut *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H41.
------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (D) (A) (B) H31).
------------------------------- assert (* AndElim *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C)) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
exact H45.
------------------------------ assert (* Cut *) (euclidean__axioms.TS B D C E) as H42.
------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (D) (C) (B) (A) (E) (H41) H40).
------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B F E) /\ ((euclidean__axioms.Col D C F) /\ (euclidean__axioms.nCol D C B))) as H43.
-------------------------------- exact H42.
-------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B F E) /\ ((euclidean__axioms.Col D C F) /\ (euclidean__axioms.nCol D C B)))) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [F H44].
assert (* AndElim *) ((euclidean__axioms.BetS B F E) /\ ((euclidean__axioms.Col D C F) /\ (euclidean__axioms.nCol D C B))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ (euclidean__axioms.nCol D C B)) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* Cut *) (euclidean__axioms.BetS E F B) as H49.
------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (F) (E) H45).
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E D A) as H50.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (E) H37).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H51.
-------------------------------------- right.
right.
right.
right.
left.
exact H50.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H52.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A))) as H52.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (D) (A) H50).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A))) as H53.
----------------------------------------- exact H52.
----------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A)) as H55.
------------------------------------------ exact H54.
------------------------------------------ destruct H55 as [H55 H56].
exact H55.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H53.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A))) as H53.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (D) (A) H50).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A))) as H54.
------------------------------------------ exact H53.
------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E A)) as H56.
------------------------------------------- exact H55.
------------------------------------------- destruct H56 as [H56 H57].
exact H57.
---------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H54.
----------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H54.
------------------------------------------ exact H29.
------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------------------------------- exact H54.
------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H55.
-------------------------------------------- exact __TmpHyp.
-------------------------------------------- destruct H55 as [x H55].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H56.
--------------------------------------------- exact H55.
--------------------------------------------- destruct H56 as [x0 H56].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H57.
---------------------------------------------- exact H56.
---------------------------------------------- destruct H57 as [x1 H57].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H58.
----------------------------------------------- exact H57.
----------------------------------------------- destruct H58 as [x2 H58].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H59.
------------------------------------------------ exact H58.
------------------------------------------------ destruct H59 as [x3 H59].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H60.
------------------------------------------------- exact H59.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H62.
-------------------------------------------------- exact H61.
-------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H64.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H66.
---------------------------------------------------- exact H65.
---------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H68.
----------------------------------------------------- exact H67.
----------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H70.
------------------------------------------------------ exact H69.
------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H72.
------------------------------------------------------- exact H71.
------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H74.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H76.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H78.
---------------------------------------------------------- exact H77.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80.
----------------------------------------------------------- exact H28.
----------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------ exact H80.
------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H81.
------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------- destruct H81 as [x4 H81].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
-------------------------------------------------------------- exact H81.
-------------------------------------------------------------- destruct H82 as [x5 H82].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H83.
--------------------------------------------------------------- exact H82.
--------------------------------------------------------------- destruct H83 as [x6 H83].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H84.
---------------------------------------------------------------- exact H83.
---------------------------------------------------------------- destruct H84 as [x7 H84].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H85.
----------------------------------------------------------------- exact H84.
----------------------------------------------------------------- destruct H85 as [x8 H85].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H86.
------------------------------------------------------------------ exact H85.
------------------------------------------------------------------ destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H88.
------------------------------------------------------------------- exact H87.
------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H90.
-------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H92.
--------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H94.
---------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H96.
----------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H98.
------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------ destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H100.
------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H102.
-------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H104.
--------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H106.
---------------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H107.
------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------ destruct H107 as [x9 H107].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H108.
------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------- destruct H108 as [x10 H108].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H109.
-------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------- destruct H109 as [x11 H109].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H110.
--------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------- destruct H110 as [x12 H110].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H111.
---------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------- destruct H111 as [x13 H111].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H112.
----------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H114.
------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H116.
------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H118.
-------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H120.
--------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H122.
---------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H124.
----------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H126.
------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H128.
------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H130.
-------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
exact H102.
----------------------------------------- assert (* Cut *) (~(B = C)) as H55.
------------------------------------------ intro H55.
assert (* Cut *) (euclidean__axioms.Col D B C) as H56.
------------------------------------------- right.
right.
left.
exact H55.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H57.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H57.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (C) H56).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H58.
---------------------------------------------- exact H57.
---------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D)))) as H60.
----------------------------------------------- exact H59.
----------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))) as H62.
------------------------------------------------ exact H61.
------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D)) as H64.
------------------------------------------------- exact H63.
------------------------------------------------- destruct H64 as [H64 H65].
exact H64.
-------------------------------------------- apply (@H39).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (A)).
----------------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False (D) (C) (B) (H48) H57).


------------------------------------------ assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS B C S) /\ (euclidean__axioms.Cong C S B C)) as H56.
------------------------------------------- apply (@lemma__extension.lemma__extension (B) (C) (B) (C) (H55) H55).
------------------------------------------- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS B C S) /\ (euclidean__axioms.Cong C S B C))) as H57.
-------------------------------------------- exact H56.
-------------------------------------------- destruct H57 as [S H57].
assert (* AndElim *) ((euclidean__axioms.BetS B C S) /\ (euclidean__axioms.Cong C S B C)) as H58.
--------------------------------------------- exact H57.
--------------------------------------------- destruct H58 as [H58 H59].
assert (* Cut *) (euclidean__axioms.BetS S C B) as H60.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (S) H58).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S C B) as H61.
----------------------------------------------- right.
right.
right.
right.
left.
exact H60.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq S B) as H62.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H62.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (S) (C) (B) H60).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H63.
-------------------------------------------------- exact H62.
-------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B)) as H65.
--------------------------------------------------- exact H64.
--------------------------------------------------- destruct H65 as [H65 H66].
exact H66.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H63.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H63.
-------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (S) (C) (B) H60).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H64.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B)) as H66.
---------------------------------------------------- exact H65.
---------------------------------------------------- destruct H66 as [H66 H67].
exact H64.
------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E A S B)) as H64.
-------------------------------------------------- intro H64.
assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq S B) /\ ((euclidean__axioms.Col E A R) /\ (euclidean__axioms.Col S B R)))) as H65.
--------------------------------------------------- exact H64.
--------------------------------------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq S B) /\ ((euclidean__axioms.Col E A R) /\ (euclidean__axioms.Col S B R))))) as H66.
---------------------------------------------------- exact H65.
---------------------------------------------------- destruct H66 as [R H66].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq S B) /\ ((euclidean__axioms.Col E A R) /\ (euclidean__axioms.Col S B R)))) as H67.
----------------------------------------------------- exact H66.
----------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq S B) /\ ((euclidean__axioms.Col E A R) /\ (euclidean__axioms.Col S B R))) as H69.
------------------------------------------------------ exact H68.
------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E A R) /\ (euclidean__axioms.Col S B R)) as H71.
------------------------------------------------------- exact H70.
------------------------------------------------------- destruct H71 as [H71 H72].
assert (* Cut *) (euclidean__axioms.Col B C S) as H73.
-------------------------------------------------------- right.
right.
right.
right.
left.
exact H58.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S B C) as H74.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B S) /\ ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))))) as H74.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (S) H73).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B S) /\ ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))))) as H75.
----------------------------------------------------------- exact H74.
----------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B)))) as H77.
------------------------------------------------------------ exact H76.
------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))) as H79.
------------------------------------------------------------- exact H78.
------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B)) as H81.
-------------------------------------------------------------- exact H80.
-------------------------------------------------------------- destruct H81 as [H81 H82].
exact H79.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C R) as H75.
---------------------------------------------------------- assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as H75.
----------------------------------------------------------- apply (@euclidean__tactics.eq__or__neq (B) R).
----------------------------------------------------------- assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as H76.
------------------------------------------------------------ exact H75.
------------------------------------------------------------ assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as __TmpHyp.
------------------------------------------------------------- exact H76.
------------------------------------------------------------- assert (B = R \/ euclidean__axioms.neq B R) as H77.
-------------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------------- destruct H77 as [H77|H77].
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C R) as H78.
---------------------------------------------------------------- right.
left.
exact H77.
---------------------------------------------------------------- exact H78.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B R C) as H78.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (R) (C)).
-----------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (B) (R) (C) (H78)).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (S) (B) (R) (C) (H72) (H74) H69).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C R) as H79.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R B C) /\ ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C B R) /\ ((euclidean__axioms.Col B C R) /\ (euclidean__axioms.Col C R B))))) as H79.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (R) (C) H78).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col R B C) /\ ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C B R) /\ ((euclidean__axioms.Col B C R) /\ (euclidean__axioms.Col C R B))))) as H80.
------------------------------------------------------------------- exact H79.
------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C B R) /\ ((euclidean__axioms.Col B C R) /\ (euclidean__axioms.Col C R B)))) as H82.
-------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col C B R) /\ ((euclidean__axioms.Col B C R) /\ (euclidean__axioms.Col C R B))) as H84.
--------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col B C R) /\ (euclidean__axioms.Col C R B)) as H86.
---------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H86.
----------------------------------------------------------------- exact H79.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D E) as H76.
----------------------------------------------------------- right.
right.
right.
right.
left.
exact H37.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H77.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H77.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H76).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H78.
-------------------------------------------------------------- exact H77.
-------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H80.
--------------------------------------------------------------- exact H79.
--------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H82.
---------------------------------------------------------------- exact H81.
---------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H84.
----------------------------------------------------------------- exact H83.
----------------------------------------------------------------- destruct H84 as [H84 H85].
exact H82.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A D) as H78.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H78.
-------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (S) (C) (B) H60).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B))) as H79.
--------------------------------------------------------------- exact H78.
--------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq S C) /\ (euclidean__axioms.neq S B)) as H81.
---------------------------------------------------------------- exact H80.
---------------------------------------------------------------- destruct H81 as [H81 H82].
exact H34.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D R) as H79.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (D) (R)).
---------------------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (R) (H79)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (D) (R) (H77) (H71) H67).


-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H80.
--------------------------------------------------------------- exists R.
split.
---------------------------------------------------------------- exact H78.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H55.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H79.
------------------------------------------------------------------ exact H75.
--------------------------------------------------------------- apply (@H39).
----------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (A)).
-----------------------------------------------------------------intro H81.
apply (@H54 H80).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F C) as H65.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))))) as H65.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (F) H47).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))))) as H66.
----------------------------------------------------- exact H65.
----------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D)))) as H68.
------------------------------------------------------ exact H67.
------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))) as H70.
------------------------------------------------------- exact H69.
------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D)) as H72.
-------------------------------------------------------- exact H71.
-------------------------------------------------------- destruct H72 as [H72 H73].
exact H72.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D F C) as H66.
---------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (E) (A) (S) (B) (D) (C) (F) (H51) (H61) (H53) (H62) (H52) (H63) (H64) (H49) H47).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C F D) as H67.
----------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (F) (C) H66).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H68.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H68.
------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (E) H37).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H69.
-------------------------------------------------------- exact H68.
-------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E)) as H71.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- destruct H71 as [H71 H72].
exact H72.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E A) as H69.
------------------------------------------------------- exact H53.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B S) as H70.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C S) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B S))) as H70.
--------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (C) (S) H58).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C S) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B S))) as H71.
---------------------------------------------------------- exact H70.
---------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B S)) as H73.
----------------------------------------------------------- exact H72.
----------------------------------------------------------- destruct H73 as [H73 H74].
exact H74.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq S B) as H71.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E A C)) as H72.
---------------------------------------------------------- intro H72.
assert (* Cut *) (euclidean__axioms.Col B C S) as H73.
----------------------------------------------------------- right.
right.
right.
right.
left.
exact H58.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S B C) as H74.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C B S) /\ ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))))) as H74.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (S) H73).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B S) /\ ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C S B) /\ ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B)))) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col S B C) /\ ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B))) as H79.
---------------------------------------------------------------- exact H78.
---------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col B S C) /\ (euclidean__axioms.Col S C B)) as H81.
----------------------------------------------------------------- exact H80.
----------------------------------------------------------------- destruct H81 as [H81 H82].
exact H79.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E A S B) as H75.
------------------------------------------------------------- exists C.
split.
-------------------------------------------------------------- exact H69.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- exact H74.
------------------------------------------------------------- apply (@H39).
--------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (A)).
---------------------------------------------------------------intro H76.
apply (@H64 H75).


---------------------------------------------------------- assert (* Cut *) (exists (H73: euclidean__axioms.Point), (euclidean__axioms.BetS C H73 A) /\ (euclidean__axioms.BetS E F H73)) as H73.
----------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (C) (E) (D) (F) (A) (H67) (H50)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (E) (A) (C) H72).

----------------------------------------------------------- assert (exists H74: euclidean__axioms.Point, ((euclidean__axioms.BetS C H74 A) /\ (euclidean__axioms.BetS E F H74))) as H75.
------------------------------------------------------------ exact H73.
------------------------------------------------------------ destruct H75 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.BetS C H74 A) /\ (euclidean__axioms.BetS E F H74)) as H76.
------------------------------------------------------------- exact H75.
------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* Cut *) (euclidean__axioms.Col E F H74) as H78.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H77.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F B) as H79.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H49.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H80.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F H74) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E H74))) as H80.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (F) (H74) H77).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F H74) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E H74))) as H81.
------------------------------------------------------------------ exact H80.
------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E H74)) as H83.
------------------------------------------------------------------- exact H82.
------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H83.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H81.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H80).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E H74) as H82.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F E H74) /\ ((euclidean__axioms.Col F H74 E) /\ ((euclidean__axioms.Col H74 E F) /\ ((euclidean__axioms.Col E H74 F) /\ (euclidean__axioms.Col H74 F E))))) as H82.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (H74) H78).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E H74) /\ ((euclidean__axioms.Col F H74 E) /\ ((euclidean__axioms.Col H74 E F) /\ ((euclidean__axioms.Col E H74 F) /\ (euclidean__axioms.Col H74 F E))))) as H83.
-------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col F H74 E) /\ ((euclidean__axioms.Col H74 E F) /\ ((euclidean__axioms.Col E H74 F) /\ (euclidean__axioms.Col H74 F E)))) as H85.
--------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col H74 E F) /\ ((euclidean__axioms.Col E H74 F) /\ (euclidean__axioms.Col H74 F E))) as H87.
---------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col E H74 F) /\ (euclidean__axioms.Col H74 F E)) as H89.
----------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H83.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F E B) as H83.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))))) as H83.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (B) H79).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))))) as H84.
--------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E)))) as H86.
---------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))) as H88.
----------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E)) as H90.
------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------ destruct H90 as [H90 H91].
exact H84.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H74 B) as H84.
-------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (H74) (B)).
---------------------------------------------------------------------intro H84.
apply (@euclidean__tactics.Col__nCol__False (E) (H74) (B) (H84)).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (E) (H74) (B) (H82) (H83) H81).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A H74 C) as H85.
--------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (H74) (A) H76).
--------------------------------------------------------------------- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS A E R) /\ (euclidean__axioms.Cong E R A E)) as H86.
---------------------------------------------------------------------- apply (@lemma__extension.lemma__extension (A) (E) (A) (E) (H68) H68).
---------------------------------------------------------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS A E R) /\ (euclidean__axioms.Cong E R A E))) as H87.
----------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------- destruct H87 as [R H87].
assert (* AndElim *) ((euclidean__axioms.BetS A E R) /\ (euclidean__axioms.Cong E R A E)) as H88.
------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------ destruct H88 as [H88 H89].
assert (* Cut *) (euclidean__axioms.Col A E R) as H90.
------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H88.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H91.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E R) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R))) as H91.
--------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (R) H88).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E R) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R))) as H92.
---------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R)) as H94.
----------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H94.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A R) as H92.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E R) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R))) as H92.
---------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (R) H88).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E R) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R))) as H93.
----------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R)) as H95.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ destruct H95 as [H95 H96].
exact H96.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H93.
---------------------------------------------------------------------------- exact H63.
---------------------------------------------------------------------------- assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.BetS C B T) /\ (euclidean__axioms.Cong B T C B)) as H94.
----------------------------------------------------------------------------- apply (@lemma__extension.lemma__extension (C) (B) (C) (B) (H93) H93).
----------------------------------------------------------------------------- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.BetS C B T) /\ (euclidean__axioms.Cong B T C B))) as H95.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ destruct H95 as [T H95].
assert (* AndElim *) ((euclidean__axioms.BetS C B T) /\ (euclidean__axioms.Cong B T C B)) as H96.
------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* Cut *) (~(euclidean__defs.Meet A R T C)) as H98.
-------------------------------------------------------------------------------- intro H98.
assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq T C) /\ ((euclidean__axioms.Col A R p) /\ (euclidean__axioms.Col T C p)))) as H99.
--------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq T C) /\ ((euclidean__axioms.Col A R p) /\ (euclidean__axioms.Col T C p))))) as H100.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- destruct H100 as [p H100].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq T C) /\ ((euclidean__axioms.Col A R p) /\ (euclidean__axioms.Col T C p)))) as H101.
----------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq T C) /\ ((euclidean__axioms.Col A R p) /\ (euclidean__axioms.Col T C p))) as H103.
------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col A R p) /\ (euclidean__axioms.Col T C p)) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* Cut *) (euclidean__axioms.Col A E R) as H107.
-------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B T) as H108.
--------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H96.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D E) as H109.
---------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H37.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R A p) as H110.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R A p) /\ ((euclidean__axioms.Col R p A) /\ ((euclidean__axioms.Col p A R) /\ ((euclidean__axioms.Col A p R) /\ (euclidean__axioms.Col p R A))))) as H110.
------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (R) (p) H105).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col R A p) /\ ((euclidean__axioms.Col R p A) /\ ((euclidean__axioms.Col p A R) /\ ((euclidean__axioms.Col A p R) /\ (euclidean__axioms.Col p R A))))) as H111.
------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col R p A) /\ ((euclidean__axioms.Col p A R) /\ ((euclidean__axioms.Col A p R) /\ (euclidean__axioms.Col p R A)))) as H113.
-------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col p A R) /\ ((euclidean__axioms.Col A p R) /\ (euclidean__axioms.Col p R A))) as H115.
--------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col A p R) /\ (euclidean__axioms.Col p R A)) as H117.
---------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H111.
----------------------------------------------------------------------------------------- assert (* Cut *) (A = A) as H111.
------------------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A R A) as H112.
------------------------------------------------------------------------------------------- right.
left.
exact H111.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H113.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H113.
--------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H109).
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H114.
---------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H116.
----------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H118.
------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H120.
------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H118.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E R) as H114.
--------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A R) as H115.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A R) /\ ((euclidean__axioms.Col E R A) /\ ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A))))) as H115.
----------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (R) H114).
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A R) /\ ((euclidean__axioms.Col E R A) /\ ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A))))) as H116.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col E R A) /\ ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A)))) as H118.
------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A))) as H120.
-------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A)) as H122.
--------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
exact H116.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H116.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T))) as H116.
------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (T) H96).
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T))) as H117.
------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T)) as H119.
-------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
exact H34.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D R) as H117.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (D) (R)).
-------------------------------------------------------------------------------------------------intro H117.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (R) (H117)).
--------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (D) (R) (H113) (H115) H69).


------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A R D) as H118.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A R) /\ ((euclidean__axioms.Col D R A) /\ ((euclidean__axioms.Col R A D) /\ ((euclidean__axioms.Col A R D) /\ (euclidean__axioms.Col R D A))))) as H118.
-------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (R) H117).
-------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A R) /\ ((euclidean__axioms.Col D R A) /\ ((euclidean__axioms.Col R A D) /\ ((euclidean__axioms.Col A R D) /\ (euclidean__axioms.Col R D A))))) as H119.
--------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col D R A) /\ ((euclidean__axioms.Col R A D) /\ ((euclidean__axioms.Col A R D) /\ (euclidean__axioms.Col R D A)))) as H121.
---------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col R A D) /\ ((euclidean__axioms.Col A R D) /\ (euclidean__axioms.Col R D A))) as H123.
----------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col A R D) /\ (euclidean__axioms.Col R D A)) as H125.
------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
exact H125.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D p) as H119.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (D) (p)).
---------------------------------------------------------------------------------------------------intro H119.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (p) (H119)).
----------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (A) (R) (A) (D) (p) (H101) (H112) (H118) H105).


-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B T C) as H120.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C T) /\ ((euclidean__axioms.Col B T C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C))))) as H120.
---------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (T) H108).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C T) /\ ((euclidean__axioms.Col B T C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C))))) as H121.
----------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col B T C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C)))) as H123.
------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C))) as H125.
------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C)) as H127.
-------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H123.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col T C B) as H121.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col T B C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C B T) /\ ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B))))) as H121.
----------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (T) (C) H120).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col T B C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C B T) /\ ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B))))) as H122.
------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C B T) /\ ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B)))) as H124.
------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col C B T) /\ ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B))) as H126.
-------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B)) as H128.
--------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H124.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C T) as H122.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T))) as H122.
------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (T) H96).
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T))) as H123.
------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C T)) as H125.
-------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
exact H126.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq T C) as H123.
------------------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B p) as H124.
------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (p)).
--------------------------------------------------------------------------------------------------------intro H124.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (p) (H124)).
---------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (T) (C) (B) (p) (H121) (H106) H123).


------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C p) as H125.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H125.
--------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (p) H124).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H126.
---------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)))) as H128.
----------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))) as H130.
------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)) as H132.
------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
exact H126.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H126.
--------------------------------------------------------------------------------------------------------- exists p.
split.
---------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------------------ exact H125.
--------------------------------------------------------------------------------------------------------- apply (@H39).
----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (A)).
-----------------------------------------------------------------------------------------------------------intro H127.
apply (@H54 H126).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS T B C) as H99.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (B) (T) H96).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col T B C) as H100.
---------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H99.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq T C) as H101.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))) as H101.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (T) (B) (C) H99).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))) as H102.
------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)) as H104.
-------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H105.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H102.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))) as H102.
------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (T) (B) (C) H99).
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))) as H103.
-------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)) as H105.
--------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H103.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E B H74) as H103.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H74 E B) /\ ((euclidean__axioms.Col H74 B E) /\ ((euclidean__axioms.Col B E H74) /\ ((euclidean__axioms.Col E B H74) /\ (euclidean__axioms.Col B H74 E))))) as H103.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (H74) (B) H84).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H74 E B) /\ ((euclidean__axioms.Col H74 B E) /\ ((euclidean__axioms.Col B E H74) /\ ((euclidean__axioms.Col E B H74) /\ (euclidean__axioms.Col B H74 E))))) as H104.
--------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col H74 B E) /\ ((euclidean__axioms.Col B E H74) /\ ((euclidean__axioms.Col E B H74) /\ (euclidean__axioms.Col B H74 E)))) as H106.
---------------------------------------------------------------------------------------- exact H105.
---------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col B E H74) /\ ((euclidean__axioms.Col E B H74) /\ (euclidean__axioms.Col B H74 E))) as H108.
----------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col E B H74) /\ (euclidean__axioms.Col B H74 E)) as H110.
------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
exact H110.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E H74 B) as H104.
-------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (A) (R) (T) (C) (E) (B) (H74) (H90) (H100) (H92) (H101) (H91) (H102) (H98) (H85) H103).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B H74 E) as H105.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (H74) (B) H104).
--------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B E A)) as H106.
---------------------------------------------------------------------------------------- intro H106.
assert (* Cut *) (euclidean__axioms.Col A D E) as H107.
----------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H37.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H108.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H108.
------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H107).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H109.
-------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H111.
--------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H113.
---------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H115.
----------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
exact H113.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E A B) as H109.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))))) as H109.
-------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (A) H106).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))))) as H110.
--------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B)))) as H112.
---------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))) as H114.
----------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B)) as H116.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
exact H112.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D B) as H110.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (D) (B)).
---------------------------------------------------------------------------------------------intro H110.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (B) (H110)).
----------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (D) (B) (H108) (H109) H69).


-------------------------------------------------------------------------------------------- assert (* Cut *) (B = B) as H111.
--------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) B).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H112.
---------------------------------------------------------------------------------------------- right.
left.
exact H111.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H113.
----------------------------------------------------------------------------------------------- exists B.
split.
------------------------------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------- apply (@H39).
------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (A)).
-------------------------------------------------------------------------------------------------intro H114.
apply (@H54 H113).


---------------------------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS B M D) /\ (euclidean__axioms.BetS A M H74)) as H107.
----------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (B) (A) (E) (H74) (D) (H105) (H37)).
------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (E) (A) H106).

----------------------------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.BetS A M H74))) as H108.
------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------ destruct H108 as [M H108].
assert (* AndElim *) ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.BetS A M H74)) as H109.
------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* Cut *) (euclidean__axioms.BetS A H74 C) as H111.
-------------------------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A M C) as H112.
--------------------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (A) (M) (H74) (C) (H110) H111).
--------------------------------------------------------------------------------------------- exists M.
split.
---------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------- exact H109.
Qed.
