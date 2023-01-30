Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__04.
Require Export proposition__16.
Definition lemma__26helper : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.CongA A B C D E F) -> ((euclidean__defs.CongA B C A E F D) -> ((euclidean__axioms.Cong A B D E) -> (~(euclidean__defs.Lt E F B C))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H3.
- exact H.
- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H4.
-- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H3).
-- assert (* Cut *) (euclidean__axioms.neq A B) as H5.
--- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H5.
---- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (B) (C) H4).
---- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
exact H12.
--- assert (* Cut *) (euclidean__axioms.neq B A) as H6.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H5).
---- assert (* Cut *) (euclidean__axioms.neq B C) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H7.
------ apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (B) (C) H4).
------ assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
exact H16.
----- assert (* Cut *) (euclidean__axioms.neq C B) as H8.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H7).
------ assert (* Cut *) (euclidean__axioms.neq A C) as H9.
------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H9.
-------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (B) (C) H4).
-------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
exact H19.
------- assert (* Cut *) (euclidean__axioms.neq C A) as H10.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H9).
-------- assert (* Cut *) (~(euclidean__defs.Lt E F B C)) as H11.
--------- intro H11.
assert (* Cut *) (exists (H12: euclidean__axioms.Point), (euclidean__axioms.BetS B H12 C) /\ (euclidean__axioms.Cong B H12 E F)) as H12.
---------- exact H11.
---------- assert (exists H13: euclidean__axioms.Point, ((euclidean__axioms.BetS B H13 C) /\ (euclidean__axioms.Cong B H13 E F))) as H14.
----------- exact H12.
----------- destruct H14 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS B H13 C) /\ (euclidean__axioms.Cong B H13 E F)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H17.
------------- exact H4.
------------- assert (* Cut *) (A = A) as H18.
-------------- apply (@logic.eq__refl (Point) A).
-------------- assert (* Cut *) (euclidean__defs.Out B A A) as H19.
--------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
----------------right.
left.
exact H18.

---------------- exact H6.
--------------- assert (* Cut *) (euclidean__defs.Out B C H13) as H20.
---------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (H13)).
-----------------left.
exact H15.

----------------- exact H7.
---------------- assert (* Cut *) (euclidean__defs.CongA A B C A B H13) as H21.
----------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (A) (B) (C) (A) (H13) (H17) (H19) H20).
----------------- assert (* Cut *) (euclidean__defs.CongA A B H13 A B C) as H22.
------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (A) (B) (H13) H21).
------------------ assert (* Cut *) (euclidean__defs.CongA A B H13 D E F) as H23.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (H13) (A) (B) (C) (D) (E) (F) (H22) H0).
------------------- assert (* Cut *) (euclidean__axioms.Cong B A E D) as H24.
-------------------- assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H24.
--------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (E) H2).
--------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D)) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
exact H25.
-------------------- assert (* Cut *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H25.
--------------------- apply (@proposition__04.proposition__04 (B) (A) (H13) (E) (D) (F) (H24) (H16) H23).
--------------------- assert (* Cut *) (euclidean__defs.CongA E F D B C A) as H26.
---------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (A) (E) (F) (D) H1).
---------------------- assert (* Cut *) (~(euclidean__axioms.Col A C H13)) as H27.
----------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col H13 C A) as H28.
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H28.
------------------------- exact H25.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* Cut *) ((euclidean__axioms.Col C A H13) /\ ((euclidean__axioms.Col C H13 A) /\ ((euclidean__axioms.Col H13 A C) /\ ((euclidean__axioms.Col A H13 C) /\ (euclidean__axioms.Col H13 C A))))) as H32.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (H13) H27).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A H13) /\ ((euclidean__axioms.Col C H13 A) /\ ((euclidean__axioms.Col H13 A C) /\ ((euclidean__axioms.Col A H13 C) /\ (euclidean__axioms.Col H13 C A))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C H13 A) /\ ((euclidean__axioms.Col H13 A C) /\ ((euclidean__axioms.Col A H13 C) /\ (euclidean__axioms.Col H13 C A)))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col H13 A C) /\ ((euclidean__axioms.Col A H13 C) /\ (euclidean__axioms.Col H13 C A))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A H13 C) /\ (euclidean__axioms.Col H13 C A)) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
exact H40.
------------------------ assert (* Cut *) (euclidean__axioms.Col B H13 C) as H29.
------------------------- right.
right.
right.
right.
left.
exact H15.
------------------------- assert (* Cut *) (euclidean__axioms.Col H13 C B) as H30.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H30.
--------------------------- exact H25.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Col H13 B C) /\ ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))))) as H34.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (H13) (C) H29).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col H13 B C) /\ ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B)))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B)) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [H41 H42].
exact H37.
-------------------------- assert (* Cut *) (euclidean__axioms.neq H13 C) as H31.
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H31.
---------------------------- exact H25.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.neq H13 C) /\ ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C))) as H35.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (H13) (C) H15).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq H13 C) /\ ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C)) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
exact H36.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H32.
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H32.
----------------------------- exact H25.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
-------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H36)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (H13) (C) (A) (B) (H28) (H30) H31).


---------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H33.
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H33.
------------------------------ exact H25.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H37.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H32).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H40.
----------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H3) H33).
----------------------- assert (* Cut *) (euclidean__axioms.Triangle A C H13) as H28.
------------------------ apply (@euclidean__tactics.nCol__notCol (A) (C) (H13) H27).
------------------------ assert (* Cut *) (euclidean__axioms.BetS C H13 B) as H29.
------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H29.
-------------------------- exact H25.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (H13) (C) H15).
------------------------- assert (* Cut *) (euclidean__defs.LtA H13 C A A H13 B) as H30.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H30.
--------------------------- exact H25.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA C0 B0 A0 A0 C0 D0))) as H34.
----------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
------------------------------ apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
------------------------------ destruct __1 as [__1 __2].
exact __2.
----------------------------- apply (@H34 (A) (C) (H13) (B) (H28) H29).
-------------------------- assert (* Cut *) (euclidean__defs.Out C B H13) as H31.
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H31.
---------------------------- exact H25.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
apply (@lemma__ray4.lemma__ray4 (C) (B) (H13)).
------------------------------left.
exact H29.

------------------------------ exact H8.
--------------------------- assert (* Cut *) (A = A) as H32.
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H32.
----------------------------- exact H25.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
exact H18.
---------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H33.
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H33.
------------------------------ exact H25.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
--------------------------------right.
left.
exact H32.

-------------------------------- exact H10.
----------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H34.
------------------------------ intro H34.
assert (* Cut *) (euclidean__axioms.Col A B C) as H35.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H35.
-------------------------------- exact H25.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H34).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H44.
------------------------------- apply (@H27).
--------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (H13)).
---------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H3) H35).


------------------------------ assert (* Cut *) (euclidean__defs.CongA B C A B C A) as H35.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H35.
-------------------------------- exact H25.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (B) (C) (A)).
----------------------------------apply (@euclidean__tactics.nCol__notCol (B) (C) (A) H34).

------------------------------- assert (* Cut *) (euclidean__defs.CongA B C A H13 C A) as H36.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H36.
--------------------------------- exact H25.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (B) (C) (A) (B) (C) (A) (H13) (A) (H35) (H31) H33).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA H13 C A B C A) as H37.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H37.
---------------------------------- exact H25.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (A) (H13) (C) (A) H36).
--------------------------------- assert (* Cut *) (euclidean__defs.LtA B C A A H13 B) as H38.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H38.
----------------------------------- exact H25.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (H13) (C) (A) (A) (H13) (B) (B) (C) (A) (H30) H36).
---------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D A H13 B) as H39.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H39.
------------------------------------ exact H25.
------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (B) (C) (A) (A) (H13) (B) (E) (F) (D) (H38) H26).
----------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A H13 B)) as H40.
------------------------------------ intro H40.
assert (* Cut *) (euclidean__axioms.Col H13 B A) as H41.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H41.
-------------------------------------- exact H25.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) ((euclidean__axioms.Col H13 A B) /\ ((euclidean__axioms.Col H13 B A) /\ ((euclidean__axioms.Col B A H13) /\ ((euclidean__axioms.Col A B H13) /\ (euclidean__axioms.Col B H13 A))))) as H45.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (H13) (B) H40).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H13 A B) /\ ((euclidean__axioms.Col H13 B A) /\ ((euclidean__axioms.Col B A H13) /\ ((euclidean__axioms.Col A B H13) /\ (euclidean__axioms.Col B H13 A))))) as H46.
----------------------------------------- exact H45.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col H13 B A) /\ ((euclidean__axioms.Col B A H13) /\ ((euclidean__axioms.Col A B H13) /\ (euclidean__axioms.Col B H13 A)))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B A H13) /\ ((euclidean__axioms.Col A B H13) /\ (euclidean__axioms.Col B H13 A))) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col A B H13) /\ (euclidean__axioms.Col B H13 A)) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
exact H48.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col B H13 C) as H42.
-------------------------------------- right.
right.
right.
right.
left.
exact H15.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col H13 B C) as H43.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H43.
---------------------------------------- exact H25.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.Col H13 B C) /\ ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))))) as H47.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (H13) (C) H42).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col H13 B C) /\ ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col H13 C B) /\ ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B)))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col C B H13) /\ ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B))) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col B C H13) /\ (euclidean__axioms.Col C H13 B)) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
exact H48.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq B H13) as H44.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H44.
----------------------------------------- exact H25.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.neq H13 C) /\ ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C))) as H48.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (H13) (C) H15).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H13 C) /\ ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq B H13) /\ (euclidean__axioms.neq B C)) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
exact H51.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq H13 B) as H45.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H45.
------------------------------------------ exact H25.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (H13) H44).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H46.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H46.
------------------------------------------- exact H25.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------------------------intro H50.
apply (@H34).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H13) (B) (C) (A) (H43) (H41) H45).


------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H47.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H47.
-------------------------------------------- exact H25.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H51.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H46).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H58.
-------------------------------------------------- exact H57.
-------------------------------------------------- destruct H58 as [H58 H59].
exact H52.
------------------------------------------- apply (@H27).
--------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (H13)).
---------------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H3) H47).


------------------------------------ assert (* Cut *) (euclidean__defs.CongA A H13 B B H13 A) as H41.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H41.
-------------------------------------- exact H25.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (H13) (B)).
----------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (H13) (B) H40).

------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H13 B E F D) as H42.
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H42.
--------------------------------------- exact H25.
--------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [H44 H45].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (H13) (B) (B) (H13) (A) (E) (F) (D) (H41) H45).
-------------------------------------- assert (* Cut *) (euclidean__defs.LtA A H13 B A H13 B) as H43.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H43.
---------------------------------------- exact H25.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (E) (F) (D) (A) (H13) (B) (A) (H13) (B) (H39) H42).
--------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA A H13 B A H13 B)) as H44.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A H13 D F) /\ ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D))) as H44.
----------------------------------------- exact H25.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA B A H13 E D F) /\ (euclidean__defs.CongA B H13 A E F D)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
apply (@lemma__angletrichotomy.lemma__angletrichotomy (A) (H13) (B) (A) (H13) (B) H43).
---------------------------------------- apply (@H27).
-----------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (H13)).
------------------------------------------intro H45.
apply (@H44 H43).


--------- exact H11.
Qed.
