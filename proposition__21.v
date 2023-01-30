Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__21helper.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__TTflip.
Require Export lemma__TTflip2.
Require Export lemma__TTorder.
Require Export lemma__TTtransitive.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angleordertransitive.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Require Export proposition__16.
Require Export proposition__20.
Definition proposition__21 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.BetS A E C) -> ((euclidean__axioms.BetS B D E) -> ((euclidean__defs.TT B A A C B D D C) /\ (euclidean__defs.LtA B A C B D C)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.BetS E D B) as H2.
- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (D) (E) H1).
- assert (* Cut *) (euclidean__axioms.nCol A B C) as H3.
-- exact H.
-- assert (* Cut *) (euclidean__axioms.Col A E C) as H4.
--- right.
right.
right.
right.
left.
exact H0.
--- assert (* Cut *) (euclidean__axioms.Col A C E) as H5.
---- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H5.
----- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H4).
----- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
exact H12.
---- assert (* Cut *) (euclidean__axioms.neq A E) as H6.
----- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H6.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (C) H0).
------ assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
exact H9.
----- assert (* Cut *) (euclidean__axioms.nCol A C B) as H7.
------ assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H7.
------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H3).
------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H14.
------ assert (* Cut *) (A = A) as H8.
------- apply (@logic.eq__refl (Point) A).
------- assert (* Cut *) (euclidean__axioms.Col A C A) as H9.
-------- right.
left.
exact H8.
-------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H10.
--------- apply (@euclidean__tactics.nCol__notCol (A) (E) (B)).
----------apply (@euclidean__tactics.nCol__not__Col (A) (E) (B)).
-----------apply (@lemma__NChelper.lemma__NChelper (A) (C) (B) (A) (E) (H7) (H9) (H5) H6).


--------- assert (* Cut *) (euclidean__axioms.nCol A B E) as H11.
---------- assert (* Cut *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))))) as H11.
----------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (B) H10).
----------- assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A)))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H18.
---------- assert (* Cut *) (euclidean__axioms.Triangle A B E) as H12.
----------- exact H11.
----------- assert (* Cut *) (euclidean__defs.TG B A A E B E) as H13.
------------ apply (@proposition__20.proposition__20 (A) (B) (E) H12).
------------ assert (* Cut *) (euclidean__defs.TT B A A C B E E C) as H14.
------------- apply (@lemma__21helper.lemma__21helper (A) (B) (C) (E) (H13) H0).
------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))))) as H15.
--------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (E) H12).
--------------- assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A)))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
exact H7.
-------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H16.
--------------- exact H4.
--------------- assert (* Cut *) (euclidean__axioms.Col A C E) as H17.
---------------- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H17.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H16).
----------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
exact H24.
---------------- assert (* Cut *) (C = C) as H18.
----------------- apply (@logic.eq__refl (Point) C).
----------------- assert (* Cut *) (euclidean__axioms.Col A C C) as H19.
------------------ right.
right.
left.
exact H18.
------------------ assert (* Cut *) (euclidean__axioms.neq E C) as H20.
------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H20.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (C) H0).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H21.
--------------------- exact H20.
--------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)) as H23.
---------------------- exact H22.
---------------------- destruct H23 as [H23 H24].
exact H21.
------------------- assert (* Cut *) (euclidean__axioms.nCol E C B) as H21.
-------------------- apply (@euclidean__tactics.nCol__notCol (E) (C) (B)).
---------------------apply (@euclidean__tactics.nCol__not__Col (E) (C) (B)).
----------------------apply (@lemma__NChelper.lemma__NChelper (A) (C) (B) (E) (C) (H15) (H17) (H19) H20).


-------------------- assert (* Cut *) (euclidean__axioms.nCol E B C) as H22.
--------------------- assert (* Cut *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))))) as H22.
---------------------- apply (@lemma__NCorder.lemma__NCorder (E) (C) (B) H21).
---------------------- assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))))) as H23.
----------------------- exact H22.
----------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E)))) as H25.
------------------------ exact H24.
------------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E)) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
exact H29.
--------------------- assert (* Cut *) (euclidean__axioms.Col E D B) as H23.
---------------------- right.
right.
right.
right.
left.
exact H2.
---------------------- assert (* Cut *) (euclidean__axioms.Col E B D) as H24.
----------------------- assert (* Cut *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))))) as H24.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (B) H23).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))))) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E)))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E)) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
exact H31.
----------------------- assert (* Cut *) (E = E) as H25.
------------------------ apply (@logic.eq__refl (Point) E).
------------------------ assert (* Cut *) (euclidean__axioms.Col E B E) as H26.
------------------------- right.
left.
exact H25.
------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H27.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B))) as H27.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (D) (B) H2).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B))) as H28.
---------------------------- exact H27.
---------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B)) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
exact H30.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol E D C) as H28.
--------------------------- apply (@euclidean__tactics.nCol__notCol (E) (D) (C)).
----------------------------apply (@euclidean__tactics.nCol__not__Col (E) (D) (C)).
-----------------------------apply (@lemma__NChelper.lemma__NChelper (E) (B) (C) (E) (D) (H22) (H26) (H24) H27).


--------------------------- assert (* Cut *) (euclidean__axioms.nCol E C D) as H29.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol E C D) /\ (euclidean__axioms.nCol C D E))))) as H29.
----------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (D) (C) H28).
----------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol E C D) /\ (euclidean__axioms.nCol C D E))))) as H30.
------------------------------ exact H29.
------------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol E C D) /\ (euclidean__axioms.nCol C D E)))) as H32.
------------------------------- exact H31.
------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol E C D) /\ (euclidean__axioms.nCol C D E))) as H34.
-------------------------------- exact H33.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol E C D) /\ (euclidean__axioms.nCol C D E)) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
exact H36.
---------------------------- assert (* Cut *) (euclidean__axioms.Triangle E C D) as H30.
----------------------------- exact H29.
----------------------------- assert (* Cut *) (euclidean__defs.TG C E E D C D) as H31.
------------------------------ apply (@proposition__20.proposition__20 (E) (C) (D) H30).
------------------------------ assert (* Cut *) (euclidean__defs.TT C E E B C D D B) as H32.
------------------------------- apply (@lemma__21helper.lemma__21helper (E) (C) (B) (D) (H31) H2).
------------------------------- assert (* Cut *) (euclidean__defs.TT E B C E C D D B) as H33.
-------------------------------- apply (@lemma__TTorder.lemma__TTorder (C) (E) (E) (B) (C) (D) (D) (B) H32).
-------------------------------- assert (* Cut *) (euclidean__defs.TT B E E C C D D B) as H34.
--------------------------------- apply (@lemma__TTflip.lemma__TTflip (E) (B) (C) (E) (C) (D) (D) (B) H33).
--------------------------------- assert (* Cut *) (euclidean__defs.TT B A A C C D D B) as H35.
---------------------------------- apply (@lemma__TTtransitive.lemma__TTtransitive (B) (A) (A) (C) (B) (E) (E) (C) (C) (D) (D) (B) (H14) H34).
---------------------------------- assert (* Cut *) (euclidean__defs.TT B A A C B D D C) as H36.
----------------------------------- apply (@lemma__TTflip2.lemma__TTflip2 (B) (A) (A) (C) (C) (D) (D) (B) H35).
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E D) as H37.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol C D E) /\ ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol E D C) /\ (euclidean__axioms.nCol D C E))))) as H37.
------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (C) (D) H30).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol C D E) /\ ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol E D C) /\ (euclidean__axioms.nCol D C E))))) as H38.
-------------------------------------- exact H37.
-------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol C D E) /\ ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol E D C) /\ (euclidean__axioms.nCol D C E)))) as H40.
--------------------------------------- exact H39.
--------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol D E C) /\ ((euclidean__axioms.nCol E D C) /\ (euclidean__axioms.nCol D C E))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol E D C) /\ (euclidean__axioms.nCol D C E)) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
exact H38.
------------------------------------ assert (* Cut *) (euclidean__axioms.Triangle C E D) as H38.
------------------------------------- exact H37.
------------------------------------- assert (* Cut *) (euclidean__defs.LtA D E C C D B) as H39.
-------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA C0 B0 A0 A0 C0 D0))) as H39.
--------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
---------------------------------------- apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
---------------------------------------- destruct __1 as [__1 __2].
exact __2.
--------------------------------------- apply (@H39 (C) (E) (D) (B) (H38) H2).
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B C) as H40.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H40.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (E) (D) H38).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H41.
----------------------------------------- exact H40.
----------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)))) as H43.
------------------------------------------ exact H42.
------------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))) as H45.
------------------------------------------- exact H44.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
exact H22.
--------------------------------------- assert (* Cut *) (B = B) as H41.
---------------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B B) as H42.
----------------------------------------- right.
right.
left.
exact H41.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D B) as H43.
------------------------------------------ exact H23.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E B D) as H44.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))))) as H44.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (B) H43).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))))) as H45.
--------------------------------------------- exact H44.
--------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E)))) as H47.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))) as H49.
----------------------------------------------- exact H48.
----------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E)) as H51.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H51 as [H51 H52].
exact H51.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H45.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B E))) as H45.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (D) (E) H1).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B E))) as H46.
---------------------------------------------- exact H45.
---------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B E)) as H48.
----------------------------------------------- exact H47.
----------------------------------------------- destruct H48 as [H48 H49].
exact H48.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H46.
--------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H45).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B C) as H47.
---------------------------------------------- apply (@euclidean__tactics.nCol__notCol (D) (B) (C)).
-----------------------------------------------apply (@euclidean__tactics.nCol__not__Col (D) (B) (C)).
------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (E) (B) (C) (D) (B) (H40) (H44) (H42) H46).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A E) as H48.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))))) as H48.
------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (B) (E) H12).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))))) as H49.
------------------------------------------------- exact H48.
------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A)))) as H51.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A))) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol A E B) /\ (euclidean__axioms.nCol E B A)) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
exact H49.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B A E) as H49.
------------------------------------------------ exact H48.
------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA E A B B E C) as H50.
------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA C0 B0 A0 A0 C0 D0))) as H50.
-------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
--------------------------------------------------- apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
--------------------------------------------------- destruct __1 as [__1 __2].
exact __2.
-------------------------------------------------- apply (@H50 (B) (A) (E) (C) (H49) H0).
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A E E A B) as H51.
-------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (A) (E) H49).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A E B E C) as H52.
--------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (E) (A) (B) (B) (E) (C) (B) (A) (E) (H50) H51).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E B) as H53.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))))) as H53.
----------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (B) (C) H40).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))))) as H54.
------------------------------------------------------ exact H53.
------------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E)))) as H56.
------------------------------------------------------- exact H55.
------------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))) as H58.
-------------------------------------------------------- exact H57.
-------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E)) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [H60 H61].
exact H58.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E B B E C) as H54.
----------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (E) (B) H53).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A E C E B) as H55.
------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (A) (E) (B) (E) (C) (C) (E) (B) (H52) H54).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A E) as H56.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B))) as H56.
-------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (D) (B) H2).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B))) as H57.
--------------------------------------------------------- exact H56.
--------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E B)) as H59.
---------------------------------------------------------- exact H58.
---------------------------------------------------------- destruct H59 as [H59 H60].
exact H6.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A E C) as H57.
-------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (E) (C)).
---------------------------------------------------------right.
right.
exact H0.

--------------------------------------------------------- exact H56.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A C E) as H58.
--------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (A) (E) (C) H57).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H59.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B)))))) as H59.
----------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (A) (E) H49).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B)))))) as H60.
------------------------------------------------------------ exact H59.
------------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))))) as H62.
------------------------------------------------------------- exact H61.
------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B)))) as H64.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))) as H66.
--------------------------------------------------------------- exact H65.
--------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B)) as H68.
---------------------------------------------------------------- exact H67.
---------------------------------------------------------------- destruct H68 as [H68 H69].
exact H66.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A B B) as H60.
----------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (B) (B)).
------------------------------------------------------------right.
left.
exact H41.

------------------------------------------------------------ exact H59.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A C) as H61.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H61.
------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H15).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H62.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H64.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H66.
---------------------------------------------------------------- exact H65.
---------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H68.
----------------------------------------------------------------- exact H67.
----------------------------------------------------------------- destruct H68 as [H68 H69].
exact H66.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B A C B A C) as H62.
------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (B) (A) (C) H61).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C B A E) as H63.
-------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (B) (A) (C) (B) (A) (C) (B) (E) (H62) (H60) H58).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D B) as H64.
--------------------------------------------------------------- exact H2.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E D B) as H65.
---------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (D) (B)).
-----------------------------------------------------------------right.
right.
exact H64.

----------------------------------------------------------------- exact H27.
---------------------------------------------------------------- assert (* Cut *) (C = C) as H66.
----------------------------------------------------------------- exact H18.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E C C) as H67.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (E) (C) (C)).
-------------------------------------------------------------------right.
left.
exact H66.

------------------------------------------------------------------- exact H20.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C E D) as H68.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol C A B))))) as H68.
-------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (A) (C) H61).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol C A B))))) as H69.
--------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol C A B)))) as H71.
---------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol C A B))) as H73.
----------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol C A B)) as H75.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ destruct H75 as [H75 H76].
exact H37.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E D C E D) as H69.
-------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (C) (E) (D) H68).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E D C E B) as H70.
--------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (C) (E) (D) (C) (E) (D) (C) (B) (H69) (H67) H65).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A E C E D) as H71.
---------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (A) (E) (C) (E) (B) (C) (E) (D) (H55) H70).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C C E D) as H72.
----------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (B) (A) (E) (C) (E) (D) (B) (A) (C) (H71) H63).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D E C) as H73.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H73.
------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (E) (D) H68).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H74.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)))) as H76.
--------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))) as H78.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)) as H80.
----------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H81.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA D E C C E D) as H74.
------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (D) (E) (C) H73).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C D E C) as H75.
-------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (A) (C) (C) (E) (D) (D) (E) (C) (H72) H74).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C C D B) as H76.
--------------------------------------------------------------------------- apply (@lemma__angleordertransitive.lemma__angleordertransitive (B) (A) (C) (D) (E) (C) (C) (D) (B) (H75) H39).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B D C) as H77.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H77.
----------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (B) (C) H47).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H78.
------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)))) as H80.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))) as H82.
-------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)) as H84.
--------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H78.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B D C C D B) as H78.
----------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (D) (C) H77).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C B D C) as H79.
------------------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (A) (C) (C) (D) (B) (B) (D) (C) (H76) H78).
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H36.
------------------------------------------------------------------------------- exact H79.
Qed.
