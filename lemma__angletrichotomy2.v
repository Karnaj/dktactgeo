Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__outerconnectivity.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__sameside2.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__23C.
Definition lemma__angletrichotomy2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__axioms.nCol A B C) -> ((euclidean__axioms.nCol D E F) -> ((~(euclidean__defs.CongA A B C D E F)) -> ((~(euclidean__defs.LtA D E F A B C)) -> (euclidean__defs.LtA A B C D E F)))).
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
assert (* Cut *) (~(B = A)) as H3.
- intro H3.
assert (* Cut *) (A = B) as H4.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (B) H3).
-- assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
--- left.
exact H4.
--- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H0)).
----apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
-----intro H6.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H5).


- assert (* Cut *) (~(B = C)) as H4.
-- intro H4.
assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
--- right.
right.
left.
exact H4.
--- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H0)).
----apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
-----intro H6.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H5).


-- assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H5.
--- intro H5.
assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
---- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H6.
----- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H5).
----- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
exact H7.
---- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H0)).
-----apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
------intro H7.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H6).


--- assert (* Cut *) (exists (G: euclidean__axioms.Point) (J: euclidean__axioms.Point), (euclidean__defs.Out B A J) /\ ((euclidean__defs.CongA G B J D E F) /\ (euclidean__defs.OS G C B A))) as H6.
---- apply (@proposition__23C.proposition__23C (B) (A) (E) (D) (F) (C) (H3) (H0)).
-----apply (@euclidean__tactics.nCol__notCol (B) (A) (C) H5).

---- assert (exists G: euclidean__axioms.Point, (exists (J: euclidean__axioms.Point), (euclidean__defs.Out B A J) /\ ((euclidean__defs.CongA G B J D E F) /\ (euclidean__defs.OS G C B A)))) as H7.
----- exact H6.
----- destruct H7 as [G H7].
assert (exists J: euclidean__axioms.Point, ((euclidean__defs.Out B A J) /\ ((euclidean__defs.CongA G B J D E F) /\ (euclidean__defs.OS G C B A)))) as H8.
------ exact H7.
------ destruct H8 as [J H8].
assert (* AndElim *) ((euclidean__defs.Out B A J) /\ ((euclidean__defs.CongA G B J D E F) /\ (euclidean__defs.OS G C B A))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.CongA G B J D E F) /\ (euclidean__defs.OS G C B A)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* Cut *) (euclidean__axioms.nCol B A G) as H13.
--------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.BetS G U X) /\ ((euclidean__axioms.BetS C V X) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C)))))) as H13.
---------- exact H12.
---------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.BetS G U X) /\ ((euclidean__axioms.BetS C V X) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C)))))) as __TmpHyp.
----------- exact H13.
----------- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.BetS G U X) /\ ((euclidean__axioms.BetS C V X) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C))))))) as H14.
------------ exact __TmpHyp.
------------ destruct H14 as [x H14].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.BetS G U x) /\ ((euclidean__axioms.BetS C V x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C))))))) as H15.
------------- exact H14.
------------- destruct H15 as [x0 H15].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col B A x0) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.BetS G x0 x) /\ ((euclidean__axioms.BetS C V x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C))))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [x1 H16].
assert (* AndElim *) ((euclidean__axioms.Col B A x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.BetS G x0 x) /\ ((euclidean__axioms.BetS C x1 x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C)))))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.BetS G x0 x) /\ ((euclidean__axioms.BetS C x1 x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C))))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS G x0 x) /\ ((euclidean__axioms.BetS C x1 x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C)))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS C x1 x) /\ ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol B A G) /\ (euclidean__axioms.nCol B A C)) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
exact H25.
--------- assert (* Cut *) (~(B = G)) as H14.
---------- intro H14.
assert (* Cut *) (euclidean__axioms.Col B A G) as H15.
----------- right.
left.
exact H14.
----------- apply (@H5).
------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------intro H16.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (G) (H13) H15).


---------- assert (* Cut *) (~(A = G)) as H15.
----------- intro H15.
assert (* Cut *) (euclidean__axioms.Col B A G) as H16.
------------ right.
right.
left.
exact H15.
------------ apply (@H5).
-------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (G) (H13) H16).


----------- assert (* Cut *) (euclidean__defs.CongA D E F G B J) as H16.
------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (G) (B) (J) (D) (E) (F) H11).
------------ assert (* Cut *) (euclidean__defs.Out B J A) as H17.
------------- apply (@lemma__ray5.lemma__ray5 (B) (A) (J) H9).
------------- assert (* Cut *) (G = G) as H18.
-------------- apply (@logic.eq__refl (Point) G).
-------------- assert (* Cut *) (euclidean__defs.Out B G G) as H19.
--------------- apply (@lemma__ray4.lemma__ray4 (B) (G) (G)).
----------------right.
left.
exact H18.

---------------- exact H14.
--------------- assert (* Cut *) (euclidean__defs.CongA D E F G B A) as H20.
---------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (G) (B) (J) (G) (A) (H16) (H19) H17).
---------------- assert (* Cut *) (euclidean__axioms.nCol G B A) as H21.
----------------- apply (@euclidean__tactics.nCol__notCol (G) (B) (A)).
------------------apply (@euclidean__tactics.nCol__not__Col (G) (B) (A)).
-------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (G) (B) (A) H20).


----------------- assert (* Cut *) (~(euclidean__axioms.Col A B G)) as H22.
------------------ intro H22.
assert (* Cut *) (euclidean__axioms.Col B A G) as H23.
------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H23.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H22).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
exact H24.
------------------- apply (@H5).
--------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (G) (H13) H23).


------------------ assert (* Cut *) (euclidean__defs.CongA G B A D E F) as H23.
------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (G) (B) (A) H20).
------------------- assert (* Cut *) (euclidean__defs.CongA A B G G B A) as H24.
-------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (G)).
---------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H22).

-------------------- assert (* Cut *) (euclidean__defs.CongA A B G D E F) as H25.
--------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (G) (G) (B) (A) (D) (E) (F) (H24) H23).
--------------------- assert (* Cut *) (~(euclidean__axioms.Col A B G)) as H26.
---------------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col G B A) as H27.
----------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H27.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H26).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H35.
----------------------- apply (@H5).
------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------------------intro H28.
apply (@H22 H26).


---------------------- assert (* Cut *) (~(G = A)) as H27.
----------------------- intro H27.
assert (* Cut *) (A = G) as H28.
------------------------ apply (@eq__ind__r euclidean__axioms.Point A (fun G0: euclidean__axioms.Point => (euclidean__defs.CongA G0 B J D E F) -> ((euclidean__defs.OS G0 C B A) -> ((euclidean__axioms.nCol B A G0) -> ((~(B = G0)) -> ((~(A = G0)) -> ((euclidean__defs.CongA D E F G0 B J) -> ((G0 = G0) -> ((euclidean__defs.Out B G0 G0) -> ((euclidean__defs.CongA D E F G0 B A) -> ((euclidean__axioms.nCol G0 B A) -> ((~(euclidean__axioms.Col A B G0)) -> ((euclidean__defs.CongA G0 B A D E F) -> ((euclidean__defs.CongA A B G0 G0 B A) -> ((euclidean__defs.CongA A B G0 D E F) -> ((~(euclidean__axioms.Col A B G0)) -> (A = G0))))))))))))))))) with (x := G).
-------------------------intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
exact H34.

------------------------- exact H27.
------------------------- exact H11.
------------------------- exact H12.
------------------------- exact H13.
------------------------- exact H14.
------------------------- exact H15.
------------------------- exact H16.
------------------------- exact H18.
------------------------- exact H19.
------------------------- exact H20.
------------------------- exact H21.
------------------------- exact H22.
------------------------- exact H23.
------------------------- exact H24.
------------------------- exact H25.
------------------------- exact H26.
------------------------ assert (* Cut *) (euclidean__axioms.Col A B G) as H29.
------------------------- right.
left.
exact H28.
------------------------- apply (@H5).
--------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------intro H30.
apply (@H15 H28).


----------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS G A P) /\ (euclidean__axioms.Cong A P G A)) as H28.
------------------------ apply (@lemma__extension.lemma__extension (G) (A) (G) (A) (H27) H27).
------------------------ assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS G A P) /\ (euclidean__axioms.Cong A P G A))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [P H29].
assert (* AndElim *) ((euclidean__axioms.BetS G A P) /\ (euclidean__axioms.Cong A P G A)) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (A = A) as H32.
--------------------------- apply (@logic.eq__refl (Point) A).
--------------------------- assert (* Cut *) (euclidean__axioms.Col B A A) as H33.
---------------------------- right.
right.
left.
exact H32.
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col B A G)) as H34.
----------------------------- intro H34.
assert (* Cut *) (euclidean__axioms.Col G B A) as H35.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H35.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (G) H34).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B)))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B)) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
exact H40.
------------------------------ apply (@H5).
-------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (G) (B) (A) (H21) H35).


----------------------------- assert (* Cut *) (euclidean__defs.OS C G B A) as H35.
------------------------------ assert (* Cut *) ((euclidean__defs.OS C G B A) /\ ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B))) as H35.
------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (A) (G) (C) H12).
------------------------------- assert (* AndElim *) ((euclidean__defs.OS C G B A) /\ ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
exact H36.
------------------------------ assert (* Cut *) (euclidean__axioms.TS G B A P) as H36.
------------------------------- exists A.
split.
-------------------------------- exact H30.
-------------------------------- split.
--------------------------------- exact H33.
--------------------------------- exact H13.
------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A P) as H37.
-------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (B) (A) (C) (G) (P) (H35) H36).
-------------------------------- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS C R P) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.nCol B A C))) as H38.
--------------------------------- exact H37.
--------------------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS C R P) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.nCol B A C)))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [R H39].
assert (* AndElim *) ((euclidean__axioms.BetS C R P) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.nCol B A C))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.nCol B A C)) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__axioms.BetS P R C) as H44.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (R) (P) H40).
------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C D E F) as H45.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.TS G B C A) \/ (~(euclidean__axioms.TS G B C A))) as H45.
--------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.TS G B C A) \/ (~(euclidean__axioms.TS G B C A)))).
----------------------------------------intro H45.
assert (* Cut *) ((euclidean__axioms.TS G B C A) -> False) as H46.
----------------------------------------- intro H46.
apply (@H45).
------------------------------------------left.
exact H46.

----------------------------------------- assert (* Cut *) ((~(euclidean__axioms.TS G B C A)) -> False) as H47.
------------------------------------------ intro H47.
apply (@H45).
-------------------------------------------right.
exact H47.

------------------------------------------ assert (* Cut *) (False) as H48.
------------------------------------------- apply (@H47 H46).
------------------------------------------- assert False.
--------------------------------------------exact H48.
-------------------------------------------- contradiction.

--------------------------------------- assert (* Cut *) ((euclidean__axioms.TS G B C A) \/ (~(euclidean__axioms.TS G B C A))) as H46.
---------------------------------------- exact H45.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.TS G B C A) \/ (~(euclidean__axioms.TS G B C A))) as __TmpHyp.
----------------------------------------- exact H46.
----------------------------------------- assert (euclidean__axioms.TS G B C A \/ ~(euclidean__axioms.TS G B C A)) as H47.
------------------------------------------ exact __TmpHyp.
------------------------------------------ destruct H47 as [H47|H47].
------------------------------------------- assert (* Cut *) (exists (H48: euclidean__axioms.Point), (euclidean__axioms.BetS G H48 A) /\ ((euclidean__axioms.Col B C H48) /\ (euclidean__axioms.nCol B C G))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- assert (exists H49: euclidean__axioms.Point, ((euclidean__axioms.BetS G H49 A) /\ ((euclidean__axioms.Col B C H49) /\ (euclidean__axioms.nCol B C G)))) as H50.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H50 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.BetS G H49 A) /\ ((euclidean__axioms.Col B C H49) /\ (euclidean__axioms.nCol B C G))) as H51.
---------------------------------------------- exact H50.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col B C H49) /\ (euclidean__axioms.nCol B C G)) as H53.
----------------------------------------------- exact H52.
----------------------------------------------- destruct H53 as [H53 H54].
assert (* Cut *) (euclidean__axioms.BetS A H49 G) as H55.
------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (H49) (A) H51).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H56.
------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
--------------------------------------------------right.
left.
exact H32.

-------------------------------------------------- exact H3.
------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B H49)) as H57.
-------------------------------------------------- intro H57.
assert (* Cut *) (~(B = H49)) as H58.
--------------------------------------------------- intro H58.
assert (* Cut *) (euclidean__axioms.BetS A B G) as H59.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H49 (fun B0: euclidean__axioms.Point => (euclidean__axioms.nCol A B0 C) -> ((~(euclidean__defs.CongA A B0 C D E F)) -> ((~(euclidean__defs.LtA D E F A B0 C)) -> ((~(B0 = A)) -> ((~(B0 = C)) -> ((~(euclidean__axioms.Col B0 A C)) -> ((euclidean__defs.Out B0 A J) -> ((euclidean__defs.CongA G B0 J D E F) -> ((euclidean__defs.OS G C B0 A) -> ((euclidean__axioms.nCol B0 A G) -> ((~(B0 = G)) -> ((euclidean__defs.CongA D E F G B0 J) -> ((euclidean__defs.Out B0 J A) -> ((euclidean__defs.Out B0 G G) -> ((euclidean__defs.CongA D E F G B0 A) -> ((euclidean__axioms.nCol G B0 A) -> ((~(euclidean__axioms.Col A B0 G)) -> ((euclidean__defs.CongA G B0 A D E F) -> ((euclidean__defs.CongA A B0 G G B0 A) -> ((euclidean__defs.CongA A B0 G D E F) -> ((~(euclidean__axioms.Col A B0 G)) -> ((euclidean__axioms.Col B0 A A) -> ((~(euclidean__axioms.Col B0 A G)) -> ((euclidean__defs.OS C G B0 A) -> ((euclidean__axioms.TS G B0 A P) -> ((euclidean__axioms.TS C B0 A P) -> ((euclidean__axioms.Col B0 A R) -> ((euclidean__axioms.nCol B0 A C) -> ((euclidean__axioms.TS G B0 C A) -> ((euclidean__axioms.Col B0 C H49) -> ((euclidean__axioms.nCol B0 C G) -> ((euclidean__defs.Out B0 A A) -> ((euclidean__axioms.Col A B0 H49) -> (euclidean__axioms.BetS A B0 G))))))))))))))))))))))))))))))))))) with (x := B).
-----------------------------------------------------intro H59.
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
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
exact H55.

----------------------------------------------------- exact H58.
----------------------------------------------------- exact H.
----------------------------------------------------- exact H1.
----------------------------------------------------- exact H2.
----------------------------------------------------- exact H3.
----------------------------------------------------- exact H4.
----------------------------------------------------- exact H5.
----------------------------------------------------- exact H9.
----------------------------------------------------- exact H11.
----------------------------------------------------- exact H12.
----------------------------------------------------- exact H13.
----------------------------------------------------- exact H14.
----------------------------------------------------- exact H16.
----------------------------------------------------- exact H17.
----------------------------------------------------- exact H19.
----------------------------------------------------- exact H20.
----------------------------------------------------- exact H21.
----------------------------------------------------- exact H22.
----------------------------------------------------- exact H23.
----------------------------------------------------- exact H24.
----------------------------------------------------- exact H25.
----------------------------------------------------- exact H26.
----------------------------------------------------- exact H33.
----------------------------------------------------- exact H34.
----------------------------------------------------- exact H35.
----------------------------------------------------- exact H36.
----------------------------------------------------- exact H37.
----------------------------------------------------- exact H42.
----------------------------------------------------- exact H43.
----------------------------------------------------- exact H47.
----------------------------------------------------- exact H53.
----------------------------------------------------- exact H54.
----------------------------------------------------- exact H56.
----------------------------------------------------- exact H57.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H60.
----------------------------------------------------- right.
right.
right.
right.
left.
exact H59.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H61.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H61.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H60).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H62.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H64.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
------------------------------------------------------ apply (@H5).
-------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------------------------------intro H62.
apply (@H22 H60).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H49 B) as H59.
---------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (H49) H58).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H49 B A) as H60.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A H49) /\ ((euclidean__axioms.Col B H49 A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A H49 B) /\ (euclidean__axioms.Col H49 B A))))) as H60.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (H49) H57).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A H49) /\ ((euclidean__axioms.Col B H49 A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A H49 B) /\ (euclidean__axioms.Col H49 B A))))) as H61.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B H49 A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A H49 B) /\ (euclidean__axioms.Col H49 B A)))) as H63.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A H49 B) /\ (euclidean__axioms.Col H49 B A))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A H49 B) /\ (euclidean__axioms.Col H49 B A)) as H67.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H49 B C) as H61.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C B H49) /\ ((euclidean__axioms.Col C H49 B) /\ ((euclidean__axioms.Col H49 B C) /\ ((euclidean__axioms.Col B H49 C) /\ (euclidean__axioms.Col H49 C B))))) as H61.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (H49) H53).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B H49) /\ ((euclidean__axioms.Col C H49 B) /\ ((euclidean__axioms.Col H49 B C) /\ ((euclidean__axioms.Col B H49 C) /\ (euclidean__axioms.Col H49 C B))))) as H62.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col C H49 B) /\ ((euclidean__axioms.Col H49 B C) /\ ((euclidean__axioms.Col B H49 C) /\ (euclidean__axioms.Col H49 C B)))) as H64.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col H49 B C) /\ ((euclidean__axioms.Col B H49 C) /\ (euclidean__axioms.Col H49 C B))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B H49 C) /\ (euclidean__axioms.Col H49 C B)) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
exact H66.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A C) as H62.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------------------------------intro H62.
apply (@H5).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H49) (B) (A) (C) (H60) (H61) H59).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H63.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H63.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H62).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
exact H64.
-------------------------------------------------------- apply (@H5 H62).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B H49 A B H49) as H58.
--------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (H49)).
----------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (H49) H57).

--------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B H49 A B G) as H59.
---------------------------------------------------- exists A.
exists H49.
exists G.
split.
----------------------------------------------------- exact H55.
----------------------------------------------------- split.
------------------------------------------------------ exact H56.
------------------------------------------------------ split.
------------------------------------------------------- exact H19.
------------------------------------------------------- exact H58.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G B A A B G) as H60.
----------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (G) (B) (A) H21).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B H49 G B A) as H61.
------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (H49) (A) (B) (G) (G) (B) (A) (H59) H60).
------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col H49 B A)) as H62.
------------------------------------------------------- intro H62.
assert (* Cut *) (euclidean__axioms.Col A B H49) as H63.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B H49 A) /\ ((euclidean__axioms.Col B A H49) /\ ((euclidean__axioms.Col A H49 B) /\ ((euclidean__axioms.Col H49 A B) /\ (euclidean__axioms.Col A B H49))))) as H63.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H49) (B) (A) H62).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B H49 A) /\ ((euclidean__axioms.Col B A H49) /\ ((euclidean__axioms.Col A H49 B) /\ ((euclidean__axioms.Col H49 A B) /\ (euclidean__axioms.Col A B H49))))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B A H49) /\ ((euclidean__axioms.Col A H49 B) /\ ((euclidean__axioms.Col H49 A B) /\ (euclidean__axioms.Col A B H49)))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A H49 B) /\ ((euclidean__axioms.Col H49 A B) /\ (euclidean__axioms.Col A B H49))) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col H49 A B) /\ (euclidean__axioms.Col A B H49)) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
exact H71.
-------------------------------------------------------- apply (@H5).
---------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------intro H64.
apply (@H57 H63).


------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H49 B A A B H49) as H63.
-------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H49) (B) (A)).
---------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H49) (B) (A) H62).

-------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H49 B A G B A) as H64.
--------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (H49) (G) (B) (A) (H49) (B) (A) (H61) H63).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H49 B A D E F) as H65.
---------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (H49) (B) (A) (G) (B) (A) (D) (E) (F) (H64) H20).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B H49 H49 B A) as H66.
----------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (H49)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (H49) H57).

----------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B H49 D E F) as H67.
------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (H49) (B) (A) (D) (E) (F) (A) (B) (H49) (H65) H66).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H68.
------------------------------------------------------------- exact H56.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C G B A) as H69.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS C G B A) /\ ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B))) as H69.
--------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (A) (G) (C) H12).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS C G B A) /\ ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B))) as H70.
---------------------------------------------------------------- exact H69.
---------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.OS G C A B) /\ (euclidean__defs.OS C G A B)) as H72.
----------------------------------------------------------------- exact H71.
----------------------------------------------------------------- destruct H72 as [H72 H73].
exact H35.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A G H49) as H70.
--------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (G) (H49)).
----------------------------------------------------------------left.
exact H55.

---------------------------------------------------------------- exact H15.
--------------------------------------------------------------- assert (* Cut *) (A = A) as H71.
---------------------------------------------------------------- exact H32.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A A) as H72.
----------------------------------------------------------------- exact H33.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C H49 B A) as H73.
------------------------------------------------------------------ apply (@lemma__sameside2.lemma__sameside2 (B) (A) (A) (C) (G) (H49) (H69) (H72) H70).
------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.BetS C B H49)) as H74.
------------------------------------------------------------------- intro H74.
assert (* Cut *) (B = B) as H75.
-------------------------------------------------------------------- apply (@logic.eq__refl (Point) B).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A B) as H76.
--------------------------------------------------------------------- right.
left.
exact H75.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A H49) as H77.
---------------------------------------------------------------------- exists B.
split.
----------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------- split.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ exact H43.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS H49 B A C) as H78.
----------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (B) (A) (C) (H49) H77).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A C) as H79.
------------------------------------------------------------------------ apply (@lemma__planeseparation.lemma__planeseparation (B) (A) (C) (H49) (C) (H73) H78).
------------------------------------------------------------------------ assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS C M C) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.nCol B A C))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS C M C) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.nCol B A C)))) as H81.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- destruct H81 as [M H81].
assert (* AndElim *) ((euclidean__axioms.BetS C M C) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.nCol B A C))) as H82.
--------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.nCol B A C)) as H84.
---------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* Cut *) (~(euclidean__axioms.BetS C M C)) as H86.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennessidentity (C) M).
----------------------------------------------------------------------------- apply (@H5).
------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------------------------------------------------------------------------intro H87.
apply (@H86 H82).


------------------------------------------------------------------- assert (* Cut *) ((B = C) \/ ((B = H49) \/ ((C = H49) \/ ((euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C)))))) as H75.
-------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C H49) as H76.
--------------------------------------------------------------------- assert (* Cut *) ((B = C) \/ ((B = H49) \/ ((C = H49) \/ ((euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C)))))) as H76.
---------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------- assert (* Cut *) ((B = C) \/ ((B = H49) \/ ((C = H49) \/ ((euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C)))))) as __TmpHyp0.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- assert (B = C \/ (B = H49) \/ ((C = H49) \/ ((euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C))))) as H77.
------------------------------------------------------------------------ exact __TmpHyp0.
------------------------------------------------------------------------ destruct H77 as [H77|H77].
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H78.
-------------------------------------------------------------------------- right.
right.
left.
exact H77.
-------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C H49))) as H79.
--------------------------------------------------------------------------- intro H79.
apply (@H4 H77).
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C H49)).
----------------------------------------------------------------------------intro H80.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H81.
----------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H83.
------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H85.
------------------------------------------------------------------------------- exact H13.
------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H87.
-------------------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H89.
--------------------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))))) as H91.
---------------------------------------------------------------------------------- exact H54.
---------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H93.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H95.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H97.
------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H99.
-------------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H101.
--------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))))) as H103.
---------------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H105.
----------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H107.
------------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H109.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H111.
-------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H113.
--------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))) as H115.
---------------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H117.
----------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H119.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H121.
------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H123.
-------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H125.
--------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))) as H127.
---------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H129.
----------------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H131.
------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H133.
------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H135.
-------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H137.
--------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))) as H139.
---------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* Cut *) (False) as H141.
----------------------------------------------------------------------------------------------------------- apply (@H4 H77).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H142.
------------------------------------------------------------------------------------------------------------ apply (@H79 H80).
------------------------------------------------------------------------------------------------------------ assert False.
-------------------------------------------------------------------------------------------------------------exact H142.
------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------- assert (B = H49 \/ (C = H49) \/ ((euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C)))) as H78.
-------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------- destruct H78 as [H78|H78].
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B H49 A) as H79.
---------------------------------------------------------------------------- left.
exact H78.
---------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C H49))) as H80.
----------------------------------------------------------------------------- intro H80.
assert (* Cut *) (~(euclidean__axioms.Col B H49 A)) as H81.
------------------------------------------------------------------------------ intro H81.
assert (* Cut *) (euclidean__axioms.Col H49 B A) as H82.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H49 B A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))))) as H82.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (H49) (A) H81).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H49 B A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))))) as H83.
--------------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B)))) as H85.
---------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))) as H87.
----------------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B)) as H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
exact H83.
------------------------------------------------------------------------------- apply (@H5).
--------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------------------------------------------------------------intro H83.
apply (@H62 H82).


------------------------------------------------------------------------------ apply (@H5).
-------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------------------------------------------------------intro H82.
apply (@H81 H79).


----------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C H49)).
------------------------------------------------------------------------------intro H81.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H82.
------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H84.
-------------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H86.
--------------------------------------------------------------------------------- exact H13.
--------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H88.
---------------------------------------------------------------------------------- exact H21.
---------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H90.
----------------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))))) as H92.
------------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H94.
------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H96.
-------------------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H98.
--------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H100.
---------------------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H102.
----------------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))))) as H104.
------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H106.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H108.
-------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H110.
--------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H112.
---------------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H114.
----------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))) as H116.
------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H118.
------------------------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H120.
-------------------------------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H122.
--------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H124.
---------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H126.
----------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))) as H128.
------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H130.
------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H132.
-------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H134.
--------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H136.
---------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H138.
----------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))) as H140.
------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* Cut *) (False) as H142.
------------------------------------------------------------------------------------------------------------- apply (@H80 H81).
------------------------------------------------------------------------------------------------------------- assert False.
--------------------------------------------------------------------------------------------------------------exact H142.
-------------------------------------------------------------------------------------------------------------- contradiction.

--------------------------------------------------------------------------- assert (C = H49 \/ (euclidean__axioms.BetS C B H49) \/ ((euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C))) as H79.
---------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- destruct H79 as [H79|H79].
----------------------------------------------------------------------------- assert (* Cut *) (H49 = H49) as H80.
------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) H49).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C H49) as H81.
------------------------------------------------------------------------------- assert (* Cut *) ((B = H49) \/ (euclidean__axioms.neq B H49)) as H81.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.eq__or__neq (B) H49).
-------------------------------------------------------------------------------- assert (* Cut *) ((B = H49) \/ (euclidean__axioms.neq B H49)) as H82.
--------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------- assert (* Cut *) ((B = H49) \/ (euclidean__axioms.neq B H49)) as __TmpHyp1.
---------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------- assert (B = H49 \/ euclidean__axioms.neq B H49) as H83.
----------------------------------------------------------------------------------- exact __TmpHyp1.
----------------------------------------------------------------------------------- destruct H83 as [H83|H83].
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B H49 A) as H84.
------------------------------------------------------------------------------------- left.
exact H83.
------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C H49))) as H85.
-------------------------------------------------------------------------------------- intro H85.
assert (* Cut *) (~(euclidean__axioms.Col B H49 A)) as H86.
--------------------------------------------------------------------------------------- intro H86.
assert (* Cut *) (euclidean__axioms.Col H49 B A) as H87.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H49 B A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))))) as H87.
----------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (H49) (A) H86).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H49 B A) /\ ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))))) as H88.
------------------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------------------ destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col H49 A B) /\ ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B)))) as H90.
------------------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col A B H49) /\ ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B))) as H92.
-------------------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col B A H49) /\ (euclidean__axioms.Col A H49 B)) as H94.
--------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H88.
---------------------------------------------------------------------------------------- apply (@H5).
-----------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------------------------------------------------------------------------------------------intro H88.
apply (@H62 H87).


--------------------------------------------------------------------------------------- apply (@H5).
----------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-----------------------------------------------------------------------------------------intro H87.
apply (@H86 H84).


-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C H49)).
---------------------------------------------------------------------------------------intro H86.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H87.
---------------------------------------------------------------------------------------- exact H.
---------------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H89.
----------------------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H91.
------------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H93.
------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H95.
-------------------------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))))) as H97.
--------------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H99.
---------------------------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H101.
----------------------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H103.
------------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H105.
------------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H107.
-------------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))))) as H109.
--------------------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H111.
---------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H113.
----------------------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H115.
------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H117.
------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H119.
-------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))) as H121.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H123.
---------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H125.
----------------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H127.
------------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------------ destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H129.
------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H131.
-------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))) as H133.
--------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H135.
---------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H137.
----------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H139.
------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H141.
------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H143.
-------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))) as H145.
--------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* Cut *) (False) as H147.
---------------------------------------------------------------------------------------------------------------------- apply (@H85 H86).
---------------------------------------------------------------------------------------------------------------------- assert False.
-----------------------------------------------------------------------------------------------------------------------exact H147.
----------------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B H49 H49) as H84.
------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (H49) (H49)).
--------------------------------------------------------------------------------------right.
left.
exact H80.

-------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C H49) as H85.
-------------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point C (fun H85: euclidean__axioms.Point => (euclidean__axioms.BetS G H85 A) -> ((euclidean__axioms.Col B C H85) -> ((euclidean__axioms.BetS A H85 G) -> ((~(euclidean__axioms.Col A B H85)) -> ((euclidean__defs.CongA A B H85 A B H85) -> ((euclidean__defs.LtA A B H85 A B G) -> ((euclidean__defs.LtA A B H85 G B A) -> ((~(euclidean__axioms.Col H85 B A)) -> ((euclidean__defs.CongA H85 B A A B H85) -> ((euclidean__defs.LtA H85 B A G B A) -> ((euclidean__defs.LtA H85 B A D E F) -> ((euclidean__defs.CongA A B H85 H85 B A) -> ((euclidean__defs.LtA A B H85 D E F) -> ((euclidean__defs.Out A G H85) -> ((euclidean__defs.OS C H85 B A) -> ((~(euclidean__axioms.BetS C B H85)) -> ((H85 = H85) -> ((euclidean__axioms.neq B H85) -> ((euclidean__defs.Out B H85 H85) -> (euclidean__defs.Out B C H85))))))))))))))))))))) with (y := H49).
---------------------------------------------------------------------------------------intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
assert (* Cut *) (C = C) as H104.
---------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------- exact H103.

--------------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------------------- exact H57.
--------------------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------------------- exact H59.
--------------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------------- exact H62.
--------------------------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- assert (euclidean__axioms.BetS C B H49 \/ (euclidean__axioms.BetS B C H49) \/ (euclidean__axioms.BetS B H49 C)) as H80.
------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------ destruct H80 as [H80|H80].
------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C H49))) as H81.
-------------------------------------------------------------------------------- intro H81.
apply (@H5).
---------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------------------------------intro H82.
apply (@H74 H80).


-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C H49)).
---------------------------------------------------------------------------------intro H82.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H83.
---------------------------------------------------------------------------------- exact H.
---------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H85.
----------------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H87.
------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H89.
------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H91.
-------------------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))))) as H93.
--------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H95.
---------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H97.
----------------------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H99.
------------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------------ destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H101.
------------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H103.
-------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))))) as H105.
--------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H107.
---------------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H109.
----------------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H111.
------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------ destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H113.
------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H115.
-------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))))) as H117.
--------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H119.
---------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H121.
----------------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H123.
------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H125.
------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H127.
-------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C G)) /\ ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G)))) as H129.
--------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H131.
---------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H133.
----------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H135.
------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H137.
------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H139.
-------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G C)) /\ (~(euclidean__axioms.BetS C B G))) as H141.
--------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* Cut *) (False) as H143.
---------------------------------------------------------------------------------------------------------------- apply (@H74 H80).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H144.
----------------------------------------------------------------------------------------------------------------- apply (@H81 H82).
----------------------------------------------------------------------------------------------------------------- assert False.
------------------------------------------------------------------------------------------------------------------exact H144.
------------------------------------------------------------------------------------------------------------------ contradiction.

------------------------------------------------------------------------------- assert (euclidean__axioms.BetS B C H49 \/ euclidean__axioms.BetS B H49 C) as H81.
-------------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------------- destruct H81 as [H81|H81].
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H82.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C H49) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B H49))) as H82.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (C) (H49) H81).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C H49) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B H49))) as H83.
------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B H49)) as H85.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H85.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C H49) as H83.
----------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (H49)).
------------------------------------------------------------------------------------right.
right.
exact H81.

------------------------------------------------------------------------------------ exact H82.
----------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H82.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H49 C) /\ ((euclidean__axioms.neq B H49) /\ (euclidean__axioms.neq B C))) as H82.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (H49) (C) H81).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H49 C) /\ ((euclidean__axioms.neq B H49) /\ (euclidean__axioms.neq B C))) as H83.
------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq B H49) /\ (euclidean__axioms.neq B C)) as H85.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H86.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C H49) as H83.
----------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (H49)).
------------------------------------------------------------------------------------left.
exact H81.

------------------------------------------------------------------------------------ exact H82.
----------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H77.
---------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B H49) as H78.
----------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (A) (B) (C) (A) (H49) (H77) (H68) H76).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C D E F) as H79.
------------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (H49) (D) (E) (F) (A) (B) (C) (H67) H78).
------------------------------------------------------------------------ exact H79.
------------------------------------------- assert (* Cut *) ((B = A) \/ ((B = R) \/ ((A = R) \/ ((euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A)))))) as H48.
-------------------------------------------- exact H42.
-------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C D E F) as H49.
--------------------------------------------- assert (* Cut *) ((B = A) \/ ((B = R) \/ ((A = R) \/ ((euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A)))))) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- assert (* Cut *) ((B = A) \/ ((B = R) \/ ((A = R) \/ ((euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A)))))) as __TmpHyp0.
----------------------------------------------- exact H49.
----------------------------------------------- assert (B = A \/ (B = R) \/ ((A = R) \/ ((euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A))))) as H50.
------------------------------------------------ exact __TmpHyp0.
------------------------------------------------ destruct H50 as [H50|H50].
------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H51.
-------------------------------------------------- intro H51.
apply (@H3 H50).
-------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
---------------------------------------------------intro H52.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H53.
---------------------------------------------------- exact H.
---------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H55.
----------------------------------------------------- exact H0.
----------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H57.
------------------------------------------------------ exact H13.
------------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H59.
------------------------------------------------------- exact H21.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H61.
-------------------------------------------------------- exact H43.
-------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H63.
--------------------------------------------------------- exact H54.
--------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H65.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H67.
----------------------------------------------------------- exact H58.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H69.
------------------------------------------------------------ exact H60.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H71.
------------------------------------------------------------- exact H62.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H73.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H75.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H77.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H79.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H81.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H83.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H85.
-------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H87.
--------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H89.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H91.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H93.
------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H95.
------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H97.
-------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H99.
--------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H101.
---------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* Cut *) (False) as H103.
----------------------------------------------------------------------------- apply (@H3 H50).
----------------------------------------------------------------------------- assert (* Cut *) (False) as H104.
------------------------------------------------------------------------------ apply (@H51 H52).
------------------------------------------------------------------------------ assert False.
-------------------------------------------------------------------------------exact H104.
------------------------------------------------------------------------------- contradiction.

------------------------------------------------- assert (B = R \/ (A = R) \/ ((euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A)))) as H51.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H51 as [H51|H51].
--------------------------------------------------- assert (* Cut *) (R = B) as H52.
---------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (R) (B) H51).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C R P) as H53.
----------------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col B A R0) -> ((euclidean__axioms.BetS P R0 C) -> ((R0 = B) -> (euclidean__axioms.BetS C R0 P)))))) with (y := R).
------------------------------------------------------intro H53.
intro H54.
intro H55.
intro H56.
assert (* Cut *) (B = B) as H57.
------------------------------------------------------- exact H56.
------------------------------------------------------- exact H53.

------------------------------------------------------ exact H51.
------------------------------------------------------ exact H40.
------------------------------------------------------ exact H42.
------------------------------------------------------ exact H44.
------------------------------------------------------ exact H52.
----------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C P G)) as H54.
------------------------------------------------------ intro H54.
assert (* Cut *) (euclidean__axioms.Col C R P) as H55.
------------------------------------------------------- right.
right.
right.
right.
left.
exact H53.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B P) as H56.
-------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col B A R0) -> ((euclidean__axioms.BetS P R0 C) -> ((R0 = B) -> ((euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col C R0 P) -> (euclidean__axioms.Col C B P)))))))) with (y := R).
---------------------------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
assert (* Cut *) (B = B) as H62.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- exact H61.

--------------------------------------------------------- exact H51.
--------------------------------------------------------- exact H40.
--------------------------------------------------------- exact H42.
--------------------------------------------------------- exact H44.
--------------------------------------------------------- exact H52.
--------------------------------------------------------- exact H53.
--------------------------------------------------------- exact H55.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A P) as H57.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H30.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G P A) as H58.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))))) as H58.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (P) H57).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))))) as H59.
------------------------------------------------------------ exact H58.
------------------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G)))) as H61.
------------------------------------------------------------- exact H60.
------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))) as H63.
-------------------------------------------------------------- exact H62.
-------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G)) as H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G P C) as H59.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P C G) /\ ((euclidean__axioms.Col P G C) /\ ((euclidean__axioms.Col G C P) /\ ((euclidean__axioms.Col C G P) /\ (euclidean__axioms.Col G P C))))) as H59.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (P) (G) H54).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col P C G) /\ ((euclidean__axioms.Col P G C) /\ ((euclidean__axioms.Col G C P) /\ ((euclidean__axioms.Col C G P) /\ (euclidean__axioms.Col G P C))))) as H60.
------------------------------------------------------------- exact H59.
------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col P G C) /\ ((euclidean__axioms.Col G C P) /\ ((euclidean__axioms.Col C G P) /\ (euclidean__axioms.Col G P C)))) as H62.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col G C P) /\ ((euclidean__axioms.Col C G P) /\ (euclidean__axioms.Col G P C))) as H64.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col C G P) /\ (euclidean__axioms.Col G P C)) as H66.
---------------------------------------------------------------- exact H65.
---------------------------------------------------------------- destruct H66 as [H66 H67].
exact H67.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G P) as H60.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P))) as H60.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (A) (P) H30).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P))) as H61.
-------------------------------------------------------------- exact H60.
-------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P)) as H63.
--------------------------------------------------------------- exact H62.
--------------------------------------------------------------- destruct H63 as [H63 H64].
exact H64.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P C A) as H61.
------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (P) (C) (A)).
--------------------------------------------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False (P) (C) (A) (H61)).
---------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (P) (C) (A) (H59) (H58) H60).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P C B) as H62.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C P B) /\ (euclidean__axioms.Col P B C))))) as H62.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (P) H56).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C P B) /\ (euclidean__axioms.Col P B C))))) as H63.
---------------------------------------------------------------- exact H62.
---------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C P B) /\ (euclidean__axioms.Col P B C)))) as H65.
----------------------------------------------------------------- exact H64.
----------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C P B) /\ (euclidean__axioms.Col P B C))) as H67.
------------------------------------------------------------------ exact H66.
------------------------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col C P B) /\ (euclidean__axioms.Col P B C)) as H69.
------------------------------------------------------------------- exact H68.
------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C P) as H63.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P))) as H63.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (R) (P) H53).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P))) as H64.
----------------------------------------------------------------- exact H63.
----------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P)) as H66.
------------------------------------------------------------------ exact H65.
------------------------------------------------------------------ destruct H66 as [H66 H67].
exact H67.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P C) as H64.
---------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (P) H63).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H65.
----------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
------------------------------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H65)).
-------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (C) (A) (B) (H61) (H62) H64).


----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H66.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H66.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H65).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H67.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H69.
--------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H71.
---------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H73.
----------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H69.
------------------------------------------------------------------ apply (@H5).
-------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H66).


------------------------------------------------------ assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q R)) as H55.
------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (C) (G) (P) (R) (A) (H53) (H30)).
--------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (C) (P) (G) H54).

------------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q R))) as H56.
-------------------------------------------------------- exact H55.
-------------------------------------------------------- destruct H56 as [Q H56].
assert (* AndElim *) ((euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q R)) as H57.
--------------------------------------------------------- exact H56.
--------------------------------------------------------- destruct H57 as [H57 H58].
assert (* Cut *) (euclidean__axioms.BetS G Q B) as H59.
---------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col B A R0) -> ((euclidean__axioms.BetS P R0 C) -> ((R0 = B) -> ((euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.BetS G Q R0) -> (euclidean__axioms.BetS G Q B)))))))) with (y := R).
-----------------------------------------------------------intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
assert (* Cut *) (B = B) as H65.
------------------------------------------------------------ exact H62.
------------------------------------------------------------ exact H64.

----------------------------------------------------------- exact H51.
----------------------------------------------------------- exact H40.
----------------------------------------------------------- exact H42.
----------------------------------------------------------- exact H44.
----------------------------------------------------------- exact H52.
----------------------------------------------------------- exact H53.
----------------------------------------------------------- exact H58.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B Q G) as H60.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (Q) (B) H59).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H61.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H61.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H60).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H62.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H64.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- destruct H64 as [H64 H65].
exact H64.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B G) as H62.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H62.
-------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H60).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H63.
--------------------------------------------------------------- exact H62.
--------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H65.
---------------------------------------------------------------- exact H64.
---------------------------------------------------------------- destruct H65 as [H65 H66].
exact H66.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q G) as H63.
-------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (G)).
---------------------------------------------------------------right.
right.
exact H60.

--------------------------------------------------------------- exact H61.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G Q) as H64.
--------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (Q) (G) H63).
--------------------------------------------------------------- assert (* Cut *) (Q = Q) as H65.
---------------------------------------------------------------- apply (@logic.eq__refl (Point) Q).
---------------------------------------------------------------- assert (* Cut *) (A = A) as H66.
----------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col B A R0) -> ((euclidean__axioms.BetS P R0 C) -> ((R0 = B) -> ((euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.BetS G Q R0) -> (A = A)))))))) with (y := R).
------------------------------------------------------------------intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
assert (* Cut *) (B = B) as H72.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------- exact H32.

------------------------------------------------------------------ exact H51.
------------------------------------------------------------------ exact H40.
------------------------------------------------------------------ exact H42.
------------------------------------------------------------------ exact H44.
------------------------------------------------------------------ exact H52.
------------------------------------------------------------------ exact H53.
------------------------------------------------------------------ exact H58.
----------------------------------------------------------------- assert (* Cut *) (C = C) as H67.
------------------------------------------------------------------ apply (@logic.eq__refl (Point) C).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H68.
------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
--------------------------------------------------------------------right.
left.
exact H66.

-------------------------------------------------------------------- exact H3.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H69.
-------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
---------------------------------------------------------------------right.
left.
exact H67.

--------------------------------------------------------------------- exact H4.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G G) as H70.
--------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.Col B A R0) -> ((euclidean__axioms.BetS P R0 C) -> ((R0 = B) -> ((euclidean__axioms.BetS C R0 P) -> ((euclidean__axioms.BetS G Q R0) -> (euclidean__defs.Out B G G)))))))) with (y := R).
----------------------------------------------------------------------intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
assert (* Cut *) (B = B) as H76.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- exact H19.

---------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------- exact H42.
---------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q Q) as H71.
---------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (Q)).
-----------------------------------------------------------------------right.
left.
exact H65.

----------------------------------------------------------------------- exact H61.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A Q A Q) as H72.
----------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) Q).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B Q) as H73.
------------------------------------------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (B) Q).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B A B A) as H74.
------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) A).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B G A B Q) as H75.
-------------------------------------------------------------------------- exists A.
exists Q.
exists A.
exists Q.
split.
--------------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H64.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A Q C) as H76.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (Q) (A) H57).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B G A B C) as H77.
---------------------------------------------------------------------------- exists A.
exists Q.
exists C.
split.
----------------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H78.
----------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA D E F A B C) as H79.
------------------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (G) (A) (B) (C) (D) (E) (F) (H77) H78).
------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H80.
------------------------------------------------------------------------------- intro H80.
apply (@H2 H79).
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
--------------------------------------------------------------------------------intro H81.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H82.
--------------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H84.
---------------------------------------------------------------------------------- exact H0.
---------------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H86.
----------------------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H88.
------------------------------------------------------------------------------------ exact H21.
------------------------------------------------------------------------------------ destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H90.
------------------------------------------------------------------------------------- exact H43.
------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H92.
-------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H94.
--------------------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H96.
---------------------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H98.
----------------------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H100.
------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H102.
------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H104.
-------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H106.
--------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H108.
---------------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H110.
----------------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H112.
------------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H114.
------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H116.
-------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H118.
--------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H120.
---------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H122.
----------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H124.
------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H126.
------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H128.
-------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H130.
--------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* Cut *) (False) as H132.
---------------------------------------------------------------------------------------------------------- apply (@H2 H79).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H133.
----------------------------------------------------------------------------------------------------------- apply (@H80 H81).
----------------------------------------------------------------------------------------------------------- assert False.
------------------------------------------------------------------------------------------------------------exact H133.
------------------------------------------------------------------------------------------------------------ contradiction.

--------------------------------------------------- assert (A = R \/ (euclidean__axioms.BetS A B R) \/ ((euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A))) as H52.
---------------------------------------------------- exact H51.
---------------------------------------------------- destruct H52 as [H52|H52].
----------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H53.
------------------------------------------------------ intro H53.
assert (* Cut *) (euclidean__axioms.BetS P A G) as H54.
------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (P) H30).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P A C) as H55.
-------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B C) -> ((~(euclidean__defs.CongA A0 B C D E F)) -> ((~(euclidean__defs.LtA D E F A0 B C)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 C)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G C B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS C G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS C B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((euclidean__axioms.nCol B A0 C) -> ((~(euclidean__axioms.TS G B C A0)) -> ((~(euclidean__defs.LtA A0 B C D E F)) -> ((euclidean__axioms.BetS P A0 G) -> (euclidean__axioms.BetS P A0 C))))))))))))))))))))))))))))))))) with (x := A).
---------------------------------------------------------intro H55.
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
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
exact H44.

--------------------------------------------------------- exact H52.
--------------------------------------------------------- exact H.
--------------------------------------------------------- exact H1.
--------------------------------------------------------- exact H2.
--------------------------------------------------------- exact H3.
--------------------------------------------------------- exact H5.
--------------------------------------------------------- exact H9.
--------------------------------------------------------- exact H12.
--------------------------------------------------------- exact H13.
--------------------------------------------------------- exact H15.
--------------------------------------------------------- exact H17.
--------------------------------------------------------- exact H20.
--------------------------------------------------------- exact H21.
--------------------------------------------------------- exact H22.
--------------------------------------------------------- exact H23.
--------------------------------------------------------- exact H24.
--------------------------------------------------------- exact H25.
--------------------------------------------------------- exact H26.
--------------------------------------------------------- exact H27.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- exact H31.
--------------------------------------------------------- exact H32.
--------------------------------------------------------- exact H33.
--------------------------------------------------------- exact H34.
--------------------------------------------------------- exact H35.
--------------------------------------------------------- exact H36.
--------------------------------------------------------- exact H37.
--------------------------------------------------------- exact H42.
--------------------------------------------------------- exact H43.
--------------------------------------------------------- exact H47.
--------------------------------------------------------- exact H53.
--------------------------------------------------------- exact H54.
-------------------------------------------------------- assert (* Cut *) (G = G) as H56.
--------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B C) -> ((~(euclidean__defs.CongA A0 B C D E F)) -> ((~(euclidean__defs.LtA D E F A0 B C)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 C)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G C B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS C G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS C B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((euclidean__axioms.nCol B A0 C) -> ((~(euclidean__axioms.TS G B C A0)) -> ((~(euclidean__defs.LtA A0 B C D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 C) -> (G = G)))))))))))))))))))))))))))))))))) with (x := A).
----------------------------------------------------------intro H56.
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
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
exact H18.

---------------------------------------------------------- exact H52.
---------------------------------------------------------- exact H.
---------------------------------------------------------- exact H1.
---------------------------------------------------------- exact H2.
---------------------------------------------------------- exact H3.
---------------------------------------------------------- exact H5.
---------------------------------------------------------- exact H9.
---------------------------------------------------------- exact H12.
---------------------------------------------------------- exact H13.
---------------------------------------------------------- exact H15.
---------------------------------------------------------- exact H17.
---------------------------------------------------------- exact H20.
---------------------------------------------------------- exact H21.
---------------------------------------------------------- exact H22.
---------------------------------------------------------- exact H23.
---------------------------------------------------------- exact H24.
---------------------------------------------------------- exact H25.
---------------------------------------------------------- exact H26.
---------------------------------------------------------- exact H27.
---------------------------------------------------------- exact H30.
---------------------------------------------------------- exact H31.
---------------------------------------------------------- exact H32.
---------------------------------------------------------- exact H33.
---------------------------------------------------------- exact H34.
---------------------------------------------------------- exact H35.
---------------------------------------------------------- exact H36.
---------------------------------------------------------- exact H37.
---------------------------------------------------------- exact H42.
---------------------------------------------------------- exact H43.
---------------------------------------------------------- exact H47.
---------------------------------------------------------- exact H53.
---------------------------------------------------------- exact H54.
---------------------------------------------------------- exact H55.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G G) as H57.
---------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B C) -> ((~(euclidean__defs.CongA A0 B C D E F)) -> ((~(euclidean__defs.LtA D E F A0 B C)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 C)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G C B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS C G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS C B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((euclidean__axioms.nCol B A0 C) -> ((~(euclidean__axioms.TS G B C A0)) -> ((~(euclidean__defs.LtA A0 B C D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 C) -> (euclidean__defs.Out B G G)))))))))))))))))))))))))))))))))) with (x := A).
-----------------------------------------------------------intro H57.
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
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
exact H19.

----------------------------------------------------------- exact H52.
----------------------------------------------------------- exact H.
----------------------------------------------------------- exact H1.
----------------------------------------------------------- exact H2.
----------------------------------------------------------- exact H3.
----------------------------------------------------------- exact H5.
----------------------------------------------------------- exact H9.
----------------------------------------------------------- exact H12.
----------------------------------------------------------- exact H13.
----------------------------------------------------------- exact H15.
----------------------------------------------------------- exact H17.
----------------------------------------------------------- exact H20.
----------------------------------------------------------- exact H21.
----------------------------------------------------------- exact H22.
----------------------------------------------------------- exact H23.
----------------------------------------------------------- exact H24.
----------------------------------------------------------- exact H25.
----------------------------------------------------------- exact H26.
----------------------------------------------------------- exact H27.
----------------------------------------------------------- exact H30.
----------------------------------------------------------- exact H31.
----------------------------------------------------------- exact H32.
----------------------------------------------------------- exact H33.
----------------------------------------------------------- exact H34.
----------------------------------------------------------- exact H35.
----------------------------------------------------------- exact H36.
----------------------------------------------------------- exact H37.
----------------------------------------------------------- exact H42.
----------------------------------------------------------- exact H43.
----------------------------------------------------------- exact H47.
----------------------------------------------------------- exact H53.
----------------------------------------------------------- exact H54.
----------------------------------------------------------- exact H55.
---------------------------------------------------------- assert (* Cut *) (A = A) as H58.
----------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B C) -> ((~(euclidean__defs.CongA A0 B C D E F)) -> ((~(euclidean__defs.LtA D E F A0 B C)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 C)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G C B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS C G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS C B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((euclidean__axioms.nCol B A0 C) -> ((~(euclidean__axioms.TS G B C A0)) -> ((~(euclidean__defs.LtA A0 B C D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 C) -> (A0 = A0)))))))))))))))))))))))))))))))))) with (x := A).
------------------------------------------------------------intro H58.
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
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
exact H78.

------------------------------------------------------------ exact H52.
------------------------------------------------------------ exact H.
------------------------------------------------------------ exact H1.
------------------------------------------------------------ exact H2.
------------------------------------------------------------ exact H3.
------------------------------------------------------------ exact H5.
------------------------------------------------------------ exact H9.
------------------------------------------------------------ exact H12.
------------------------------------------------------------ exact H13.
------------------------------------------------------------ exact H15.
------------------------------------------------------------ exact H17.
------------------------------------------------------------ exact H20.
------------------------------------------------------------ exact H21.
------------------------------------------------------------ exact H22.
------------------------------------------------------------ exact H23.
------------------------------------------------------------ exact H24.
------------------------------------------------------------ exact H25.
------------------------------------------------------------ exact H26.
------------------------------------------------------------ exact H27.
------------------------------------------------------------ exact H30.
------------------------------------------------------------ exact H31.
------------------------------------------------------------ exact H32.
------------------------------------------------------------ exact H33.
------------------------------------------------------------ exact H34.
------------------------------------------------------------ exact H35.
------------------------------------------------------------ exact H36.
------------------------------------------------------------ exact H37.
------------------------------------------------------------ exact H42.
------------------------------------------------------------ exact H43.
------------------------------------------------------------ exact H47.
------------------------------------------------------------ exact H53.
------------------------------------------------------------ exact H54.
------------------------------------------------------------ exact H55.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H59.
------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------------------------------------------------right.
left.
exact H58.

------------------------------------------------------------- exact H3.
------------------------------------------------------------ assert (* Cut *) (C = C) as H60.
------------------------------------------------------------- apply (@logic.eq__refl (Point) C).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H61.
-------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
---------------------------------------------------------------right.
left.
exact H60.

--------------------------------------------------------------- exact H4.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H62.
--------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
--------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A G C)) as H63.
---------------------------------------------------------------- intro H63.
assert (* Cut *) (euclidean__defs.CongA A B G A B G) as H64.
----------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (G)).
------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).

----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B G A B C) as H65.
------------------------------------------------------------------ exists A.
exists G.
exists C.
split.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- split.
-------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------- exact H64.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA D E F A B C) as H66.
------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (G) (A) (B) (C) (D) (E) (F) (H65) H62).
------------------------------------------------------------------- apply (@H2 H66).
---------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A C G)) as H64.
----------------------------------------------------------------- intro H64.
assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H65.
------------------------------------------------------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA A B C A B G) as H66.
------------------------------------------------------------------- exists A.
exists C.
exists G.
split.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H59.
--------------------------------------------------------------------- split.
---------------------------------------------------------------------- exact H57.
---------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C D E F) as H67.
-------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (A) (B) (G) (D) (E) (F) (H66) H62).
-------------------------------------------------------------------- apply (@H5).
---------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------------------intro H68.
apply (@H53 H67).


----------------------------------------------------------------- assert (* Cut *) (C = G) as H65.
------------------------------------------------------------------ apply (@lemma__outerconnectivity.lemma__outerconnectivity (P) (A) (C) (G) (H55) (H54) (H64) H63).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H66.
------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B G A B C) as H67.
-------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((euclidean__axioms.BetS P A C0) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((~(euclidean__axioms.BetS A G C0)) -> ((~(euclidean__axioms.BetS A C0 G)) -> ((euclidean__defs.CongA A B C0 A B C0) -> (euclidean__defs.CongA A B G A B C0))))))))))))))))))))) with (x := C).
---------------------------------------------------------------------intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B G) -> ((~(euclidean__defs.LtA D E F A0 B G)) -> ((~(euclidean__defs.CongA A0 B G D E F)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((~(euclidean__axioms.TS G B G A0)) -> ((euclidean__axioms.nCol B A0 G) -> ((~(euclidean__defs.LtA A0 B G D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 G) -> ((A0 = A0) -> ((euclidean__defs.Out B A0 A0) -> ((euclidean__defs.CongA D E F A0 B G) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((euclidean__defs.CongA A0 B G A0 B G) -> (euclidean__defs.CongA A0 B G A0 B G)))))))))))))))))))))))))))))))))))))))) with (x := A).
----------------------------------------------------------------------intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
assert (* Cut *) (R = R) as H124.
----------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------- exact H123.

---------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------- exact H67.
---------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------- exact H9.
---------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------- exact H13.
---------------------------------------------------------------------- exact H15.
---------------------------------------------------------------------- exact H17.
---------------------------------------------------------------------- exact H20.
---------------------------------------------------------------------- exact H21.
---------------------------------------------------------------------- exact H22.
---------------------------------------------------------------------- exact H23.
---------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------- exact H25.
---------------------------------------------------------------------- exact H26.
---------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------- exact H31.
---------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------- exact H33.
---------------------------------------------------------------------- exact H34.
---------------------------------------------------------------------- exact H73.
---------------------------------------------------------------------- exact H36.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- exact H42.
---------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- exact H54.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- exact H58.
---------------------------------------------------------------------- exact H59.
---------------------------------------------------------------------- exact H62.
---------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- exact H85.

--------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------- exact H.
--------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------- exact H5.
--------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------- exact H40.
--------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------- exact H44.
--------------------------------------------------------------------- exact H47.
--------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------- exact H60.
--------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B G) as H68.
--------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((euclidean__axioms.BetS P A C0) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((~(euclidean__axioms.BetS A G C0)) -> ((~(euclidean__axioms.BetS A C0 G)) -> ((euclidean__defs.CongA A B C0 A B C0) -> ((euclidean__defs.CongA A B G A B C0) -> (euclidean__defs.CongA A B C0 A B G)))))))))))))))))))))) with (x := C).
----------------------------------------------------------------------intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B G) -> ((~(euclidean__defs.LtA D E F A0 B G)) -> ((~(euclidean__defs.CongA A0 B G D E F)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((~(euclidean__axioms.TS G B G A0)) -> ((euclidean__axioms.nCol B A0 G) -> ((~(euclidean__defs.LtA A0 B G D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 G) -> ((A0 = A0) -> ((euclidean__defs.Out B A0 A0) -> ((euclidean__defs.CongA D E F A0 B G) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((euclidean__defs.CongA A0 B G A0 B G) -> ((euclidean__defs.CongA A0 B G A0 B G) -> (euclidean__defs.CongA A0 B G A0 B G))))))))))))))))))))))))))))))))))))))))) with (x := A).
-----------------------------------------------------------------------intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
assert (* Cut *) (R = R) as H127.
------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------ exact H125.

----------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------- exact H3.
----------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------- exact H9.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------- exact H15.
----------------------------------------------------------------------- exact H17.
----------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------- exact H22.
----------------------------------------------------------------------- exact H23.
----------------------------------------------------------------------- exact H24.
----------------------------------------------------------------------- exact H25.
----------------------------------------------------------------------- exact H26.
----------------------------------------------------------------------- exact H27.
----------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------- exact H31.
----------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------- exact H86.

---------------------------------------------------------------------- exact H65.
---------------------------------------------------------------------- exact H.
---------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------- exact H5.
---------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------- exact H35.
---------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------- exact H43.
---------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------- exact H47.
---------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------- exact H60.
---------------------------------------------------------------------- exact H61.
---------------------------------------------------------------------- exact H63.
---------------------------------------------------------------------- exact H64.
---------------------------------------------------------------------- exact H66.
---------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C D E F) as H69.
---------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((euclidean__axioms.BetS P A C0) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((~(euclidean__axioms.BetS A G C0)) -> ((~(euclidean__axioms.BetS A C0 G)) -> ((euclidean__defs.CongA A B C0 A B C0) -> ((euclidean__defs.CongA A B G A B C0) -> ((euclidean__defs.CongA A B C0 A B G) -> (euclidean__defs.CongA A B C0 D E F))))))))))))))))))))))) with (x := C).
-----------------------------------------------------------------------intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
apply (@eq__ind__r euclidean__axioms.Point R (fun A0: euclidean__axioms.Point => (euclidean__axioms.nCol A0 B G) -> ((~(euclidean__defs.LtA D E F A0 B G)) -> ((~(euclidean__defs.CongA A0 B G D E F)) -> ((~(B = A0)) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.nCol B A0 G) -> ((~(A0 = G)) -> ((euclidean__defs.Out B J A0) -> ((euclidean__defs.CongA D E F G B A0) -> ((euclidean__axioms.nCol G B A0) -> ((~(euclidean__axioms.Col A0 B G)) -> ((euclidean__defs.CongA G B A0 D E F) -> ((euclidean__defs.CongA A0 B G G B A0) -> ((euclidean__defs.CongA A0 B G D E F) -> ((~(euclidean__axioms.Col A0 B G)) -> ((~(G = A0)) -> ((euclidean__axioms.BetS G A0 P) -> ((euclidean__axioms.Cong A0 P G A0) -> ((A0 = A0) -> ((euclidean__axioms.Col B A0 A0) -> ((~(euclidean__axioms.Col B A0 G)) -> ((euclidean__defs.OS G G B A0) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.TS G B A0 P) -> ((euclidean__axioms.Col B A0 R) -> ((~(euclidean__axioms.TS G B G A0)) -> ((euclidean__axioms.nCol B A0 G) -> ((~(euclidean__defs.LtA A0 B G D E F)) -> ((euclidean__axioms.BetS P A0 G) -> ((euclidean__axioms.BetS P A0 G) -> ((A0 = A0) -> ((euclidean__defs.Out B A0 A0) -> ((euclidean__defs.CongA D E F A0 B G) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((~(euclidean__axioms.BetS A0 G G)) -> ((euclidean__defs.CongA A0 B G A0 B G) -> ((euclidean__defs.CongA A0 B G A0 B G) -> ((euclidean__defs.CongA A0 B G A0 B G) -> (euclidean__defs.CongA A0 B G D E F)))))))))))))))))))))))))))))))))))))))))) with (x := A).
------------------------------------------------------------------------intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
assert (* Cut *) (R = R) as H130.
------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------- exact H105.

------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------ exact H3.
------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------ exact H17.
------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------ exact H21.
------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------ exact H23.
------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------ exact H33.
------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------ exact H87.

----------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------- exact H.
----------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------- exact H2.
----------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------- exact H37.
----------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- apply (@H1 H69).
------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
-------------------------------------------------------intro H54.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H55.
-------------------------------------------------------- exact H.
-------------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H57.
--------------------------------------------------------- exact H0.
--------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H59.
---------------------------------------------------------- exact H13.
---------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H61.
----------------------------------------------------------- exact H21.
----------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H63.
------------------------------------------------------------ exact H43.
------------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H65.
------------------------------------------------------------- exact H56.
------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H67.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H69.
--------------------------------------------------------------- exact H60.
--------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H71.
---------------------------------------------------------------- exact H62.
---------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H73.
----------------------------------------------------------------- exact H64.
----------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H75.
------------------------------------------------------------------ exact H66.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H77.
------------------------------------------------------------------- exact H68.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H79.
-------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H81.
--------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H83.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H85.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H87.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H89.
------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H91.
-------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H93.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H95.
---------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H97.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H99.
------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------ destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H101.
------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H103.
-------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* Cut *) (False) as H105.
--------------------------------------------------------------------------------- apply (@H53 H54).
--------------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------------exact H105.
---------------------------------------------------------------------------------- contradiction.

----------------------------------------------------- assert (euclidean__axioms.BetS A B R \/ (euclidean__axioms.BetS B A R) \/ (euclidean__axioms.BetS B R A)) as H53.
------------------------------------------------------ exact H52.
------------------------------------------------------ destruct H53 as [H53|H53].
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS R B A) as H54.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (R) H53).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B R) as H55.
--------------------------------------------------------- exact H53.
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C P A)) as H56.
---------------------------------------------------------- intro H56.
assert (* Cut *) (euclidean__axioms.Col C R P) as H57.
----------------------------------------------------------- right.
right.
right.
right.
left.
exact H40.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C P R) as H58.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col R C P) /\ ((euclidean__axioms.Col R P C) /\ ((euclidean__axioms.Col P C R) /\ ((euclidean__axioms.Col C P R) /\ (euclidean__axioms.Col P R C))))) as H58.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (R) (P) H57).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R C P) /\ ((euclidean__axioms.Col R P C) /\ ((euclidean__axioms.Col P C R) /\ ((euclidean__axioms.Col C P R) /\ (euclidean__axioms.Col P R C))))) as H59.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col R P C) /\ ((euclidean__axioms.Col P C R) /\ ((euclidean__axioms.Col C P R) /\ (euclidean__axioms.Col P R C)))) as H61.
--------------------------------------------------------------- exact H60.
--------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col P C R) /\ ((euclidean__axioms.Col C P R) /\ (euclidean__axioms.Col P R C))) as H63.
---------------------------------------------------------------- exact H62.
---------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col C P R) /\ (euclidean__axioms.Col P R C)) as H65.
----------------------------------------------------------------- exact H64.
----------------------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C P) as H59.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P))) as H59.
-------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (R) (P) H40).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P))) as H60.
--------------------------------------------------------------- exact H59.
--------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq C R) /\ (euclidean__axioms.neq C P)) as H62.
---------------------------------------------------------------- exact H61.
---------------------------------------------------------------- destruct H62 as [H62 H63].
exact H63.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A R) as H60.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (P) (A) (R)).
---------------------------------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False (P) (A) (R) (H60)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (P) (A) (R) (H56) (H58) H59).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H61.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H54.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R A B) as H62.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R))))) as H62.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (R) (B) (A) H61).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R))))) as H63.
------------------------------------------------------------------ exact H62.
------------------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R)))) as H65.
------------------------------------------------------------------- exact H64.
------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R))) as H67.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R)) as H69.
--------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H69.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R A P) as H63.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P R) /\ ((euclidean__axioms.Col A R P) /\ ((euclidean__axioms.Col R P A) /\ ((euclidean__axioms.Col P R A) /\ (euclidean__axioms.Col R A P))))) as H63.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (R) H60).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A P R) /\ ((euclidean__axioms.Col A R P) /\ ((euclidean__axioms.Col R P A) /\ ((euclidean__axioms.Col P R A) /\ (euclidean__axioms.Col R A P))))) as H64.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A R P) /\ ((euclidean__axioms.Col R P A) /\ ((euclidean__axioms.Col P R A) /\ (euclidean__axioms.Col R A P)))) as H66.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col R P A) /\ ((euclidean__axioms.Col P R A) /\ (euclidean__axioms.Col R A P))) as H68.
--------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col P R A) /\ (euclidean__axioms.Col R A P)) as H70.
---------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------- destruct H70 as [H70 H71].
exact H71.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq R A) as H64.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A))) as H64.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (R) (B) (A) H54).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A))) as H65.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A)) as H67.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B P) as H65.
------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (P)).
--------------------------------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H65)).
---------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (R) (A) (B) (P) (H62) (H63) H64).


------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A B) as H66.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H66.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (P) H65).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H67.
---------------------------------------------------------------------- exact H66.
---------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)))) as H69.
----------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))) as H71.
------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)) as H73.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A P) as H67.
--------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H30.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A G) as H68.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))))) as H68.
----------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (P) H67).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))))) as H69.
------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G)))) as H71.
------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col P G A) /\ ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G))) as H73.
-------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col G P A) /\ (euclidean__axioms.Col P A G)) as H75.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A P) as H69.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P))) as H69.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (G) (A) (P) H30).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P))) as H70.
------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G P)) as H72.
-------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------- destruct H72 as [H72 H73].
exact H70.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H70.
------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (P) H69).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B G) as H71.
------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (G)).
--------------------------------------------------------------------------intro H71.
apply (@H22).
---------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (A) (B) (G) (H66) (H68) H70).


------------------------------------------------------------------------- apply (@H5).
--------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------------------------------------------------------intro H72.
apply (@H22 H71).


---------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M P) /\ (euclidean__axioms.BetS C B M)) as H57.
----------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (A) (C) (R) (B) (P) (H55) (H40)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (C) (P) (A) H56).

----------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M P) /\ (euclidean__axioms.BetS C B M))) as H58.
------------------------------------------------------------ exact H57.
------------------------------------------------------------ destruct H58 as [M H58].
assert (* AndElim *) ((euclidean__axioms.BetS A M P) /\ (euclidean__axioms.BetS C B M)) as H59.
------------------------------------------------------------- exact H58.
------------------------------------------------------------- destruct H59 as [H59 H60].
assert (* Cut *) (euclidean__axioms.BetS P A G) as H61.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (P) H30).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P M A) as H62.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (P) H59).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M A G) as H63.
---------------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (P) (M) (A) (G) (H62) H61).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G A M) as H64.
----------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (M) (A) (G) H63).
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C M G)) as H65.
------------------------------------------------------------------ intro H65.
assert (* Cut *) (euclidean__axioms.BetS P M A) as H66.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P A G) as H67.
-------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P M G) as H68.
--------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (P) (M) (A) (G) (H66) H67).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P M G) as H69.
---------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H68.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G P) as H70.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M P G) /\ ((euclidean__axioms.Col M G P) /\ ((euclidean__axioms.Col G P M) /\ ((euclidean__axioms.Col P G M) /\ (euclidean__axioms.Col G M P))))) as H70.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (P) (M) (G) H69).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M P G) /\ ((euclidean__axioms.Col M G P) /\ ((euclidean__axioms.Col G P M) /\ ((euclidean__axioms.Col P G M) /\ (euclidean__axioms.Col G M P))))) as H71.
------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col M G P) /\ ((euclidean__axioms.Col G P M) /\ ((euclidean__axioms.Col P G M) /\ (euclidean__axioms.Col G M P)))) as H73.
-------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col G P M) /\ ((euclidean__axioms.Col P G M) /\ (euclidean__axioms.Col G M P))) as H75.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col P G M) /\ (euclidean__axioms.Col G M P)) as H77.
---------------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H73.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G C) as H71.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M C G) /\ ((euclidean__axioms.Col M G C) /\ ((euclidean__axioms.Col G C M) /\ ((euclidean__axioms.Col C G M) /\ (euclidean__axioms.Col G M C))))) as H71.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (M) (G) H65).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M C G) /\ ((euclidean__axioms.Col M G C) /\ ((euclidean__axioms.Col G C M) /\ ((euclidean__axioms.Col C G M) /\ (euclidean__axioms.Col G M C))))) as H72.
-------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col M G C) /\ ((euclidean__axioms.Col G C M) /\ ((euclidean__axioms.Col C G M) /\ (euclidean__axioms.Col G M C)))) as H74.
--------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col G C M) /\ ((euclidean__axioms.Col C G M) /\ (euclidean__axioms.Col G M C))) as H76.
---------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C G M) /\ (euclidean__axioms.Col G M C)) as H78.
----------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------------- destruct H78 as [H78 H79].
exact H74.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq M G) as H72.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G))) as H72.
-------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (M) (G) H68).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G))) as H73.
--------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G)) as H75.
---------------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H73.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G P C) as H73.
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (P) (C)).
---------------------------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False (G) (P) (C) (H73)).
----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (G) (P) (C) (H70) (H71) H72).


-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A G) as H74.
--------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H67.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G P A) as H75.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))))) as H75.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (G) H74).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))))) as H76.
------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P)))) as H78.
------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))) as H80.
-------------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P)) as H82.
--------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H80.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P G) as H76.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G))) as H76.
------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (P) (M) (G) H68).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G))) as H77.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P G)) as H79.
-------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H80.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G P) as H77.
------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (G) H76).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P C A) as H78.
------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (P) (C) (A)).
--------------------------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (P) (C) (A) (H78)).
---------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (P) (C) (A) (H73) (H75) H77).


------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C P A) as H79.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C P A) /\ ((euclidean__axioms.Col C A P) /\ ((euclidean__axioms.Col A P C) /\ ((euclidean__axioms.Col P A C) /\ (euclidean__axioms.Col A C P))))) as H79.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (C) (A) H78).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C P A) /\ ((euclidean__axioms.Col C A P) /\ ((euclidean__axioms.Col A P C) /\ ((euclidean__axioms.Col P A C) /\ (euclidean__axioms.Col A C P))))) as H80.
---------------------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col C A P) /\ ((euclidean__axioms.Col A P C) /\ ((euclidean__axioms.Col P A C) /\ (euclidean__axioms.Col A C P)))) as H82.
----------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col A P C) /\ ((euclidean__axioms.Col P A C) /\ (euclidean__axioms.Col A C P))) as H84.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col P A C) /\ (euclidean__axioms.Col A C P)) as H86.
------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H80.
-------------------------------------------------------------------------------- apply (@H5).
---------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------------------------------intro H80.
apply (@H56 H79).


------------------------------------------------------------------ assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q B)) as H66.
------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (C) (G) (M) (B) (A) (H60) (H64)).
--------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (C) (M) (G) H65).

------------------------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q B))) as H67.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- destruct H67 as [Q H67].
assert (* AndElim *) ((euclidean__axioms.BetS C Q A) /\ (euclidean__axioms.BetS G Q B)) as H68.
--------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* Cut *) (euclidean__axioms.BetS B Q G) as H70.
---------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (Q) (B) H69).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H71.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H71.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H70).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H72.
------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H74.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- destruct H74 as [H74 H75].
exact H74.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H72.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H72.
------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H70).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H73.
-------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H75.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B Q G) as H73.
------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (G)).
--------------------------------------------------------------------------right.
right.
exact H70.

-------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G Q) as H74.
-------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (Q) (G) H73).
-------------------------------------------------------------------------- assert (* Cut *) (Q = Q) as H75.
--------------------------------------------------------------------------- apply (@logic.eq__refl (Point) Q).
--------------------------------------------------------------------------- assert (* Cut *) (A = A) as H76.
---------------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------------- assert (* Cut *) (C = C) as H77.
----------------------------------------------------------------------------- apply (@logic.eq__refl (Point) C).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H78.
------------------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------------------------------------------------------------------right.
left.
exact H76.

------------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C C) as H79.
------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
--------------------------------------------------------------------------------right.
left.
exact H77.

-------------------------------------------------------------------------------- exact H4.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G G) as H80.
-------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q Q) as H81.
--------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (Q)).
----------------------------------------------------------------------------------right.
left.
exact H75.

---------------------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A Q A Q) as H82.
---------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) Q).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B Q) as H83.
----------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) Q).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H84.
------------------------------------------------------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (B) A).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B G A B Q) as H85.
------------------------------------------------------------------------------------- exists A.
exists Q.
exists A.
exists Q.
split.
-------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A Q C) as H86.
-------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (Q) (A) H68).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B G A B C) as H87.
--------------------------------------------------------------------------------------- exists A.
exists Q.
exists C.
split.
---------------------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------------------ exact H85.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H88.
---------------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA D E F A B C) as H89.
----------------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (G) (A) (B) (C) (D) (E) (F) (H87) H88).
----------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H90.
------------------------------------------------------------------------------------------ intro H90.
apply (@H2 H89).
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
-------------------------------------------------------------------------------------------intro H91.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H92.
-------------------------------------------------------------------------------------------- exact H.
-------------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H94.
--------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H96.
---------------------------------------------------------------------------------------------- exact H13.
---------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H98.
----------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H100.
------------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H102.
------------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H104.
-------------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H106.
--------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H108.
---------------------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H110.
----------------------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H112.
------------------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H114.
------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H116.
-------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H118.
--------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H120.
---------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H122.
----------------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H124.
------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H126.
------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H128.
-------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H130.
--------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H132.
---------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H134.
----------------------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H136.
------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------ destruct H136 as [H136 H137].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H138.
------------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H140.
-------------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* Cut *) (False) as H142.
--------------------------------------------------------------------------------------------------------------------- apply (@H2 H89).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H143.
---------------------------------------------------------------------------------------------------------------------- apply (@H90 H91).
---------------------------------------------------------------------------------------------------------------------- assert False.
-----------------------------------------------------------------------------------------------------------------------exact H143.
----------------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------- assert (euclidean__axioms.BetS B A R \/ euclidean__axioms.BetS B R A) as H54.
-------------------------------------------------------- exact H53.
-------------------------------------------------------- destruct H54 as [H54|H54].
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col P C B)) as H55.
---------------------------------------------------------- intro H55.
assert (* Cut *) (euclidean__axioms.Col B A R) as H56.
----------------------------------------------------------- exact H42.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P R C) as H57.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H44.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P C R) as H58.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R P C) /\ ((euclidean__axioms.Col R C P) /\ ((euclidean__axioms.Col C P R) /\ ((euclidean__axioms.Col P C R) /\ (euclidean__axioms.Col C R P))))) as H58.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (R) (C) H57).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R P C) /\ ((euclidean__axioms.Col R C P) /\ ((euclidean__axioms.Col C P R) /\ ((euclidean__axioms.Col P C R) /\ (euclidean__axioms.Col C R P))))) as H59.
--------------------------------------------------------------- exact H58.
--------------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col R C P) /\ ((euclidean__axioms.Col C P R) /\ ((euclidean__axioms.Col P C R) /\ (euclidean__axioms.Col C R P)))) as H61.
---------------------------------------------------------------- exact H60.
---------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col C P R) /\ ((euclidean__axioms.Col P C R) /\ (euclidean__axioms.Col C R P))) as H63.
----------------------------------------------------------------- exact H62.
----------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col P C R) /\ (euclidean__axioms.Col C R P)) as H65.
------------------------------------------------------------------ exact H64.
------------------------------------------------------------------ destruct H65 as [H65 H66].
exact H65.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P C) as H59.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P C))) as H59.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (R) (C) H44).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P C))) as H60.
---------------------------------------------------------------- exact H59.
---------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P C)) as H62.
----------------------------------------------------------------- exact H61.
----------------------------------------------------------------- destruct H62 as [H62 H63].
exact H63.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B R) as H60.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (R)).
----------------------------------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (R) (H60)).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (C) (B) (R) (H55) (H58) H59).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R B C) as H61.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C R) /\ ((euclidean__axioms.Col B R C) /\ ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C R B) /\ (euclidean__axioms.Col R B C))))) as H61.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (R) H60).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C R) /\ ((euclidean__axioms.Col B R C) /\ ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C R B) /\ (euclidean__axioms.Col R B C))))) as H62.
------------------------------------------------------------------ exact H61.
------------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col B R C) /\ ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C R B) /\ (euclidean__axioms.Col R B C)))) as H64.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col R C B) /\ ((euclidean__axioms.Col C R B) /\ (euclidean__axioms.Col R B C))) as H66.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col C R B) /\ (euclidean__axioms.Col R B C)) as H68.
--------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H62.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H62.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (R) H56).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H63.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B)))) as H65.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))) as H67.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B)) as H69.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B R) as H63.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R))) as H63.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (R) H54).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R))) as H64.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R)) as H66.
--------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H67.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq R B) as H64.
------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (R) H63).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H65.
-------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (C) (A)).
---------------------------------------------------------------------intro H65.
apply (@H5).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (R) (B) (A) (C) (H62) (H61) H64).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H66.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H66.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H65).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H67.
----------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H69.
------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H71.
------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H73.
-------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
--------------------------------------------------------------------- apply (@H5).
----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-----------------------------------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H66).


---------------------------------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS B Q C) /\ (euclidean__axioms.BetS P A Q)) as H56.
----------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (B) (P) (R) (A) (C) (H54) (H44)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (P) (C) (B) H55).

----------------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS B Q C) /\ (euclidean__axioms.BetS P A Q))) as H57.
------------------------------------------------------------ exact H56.
------------------------------------------------------------ destruct H57 as [Q H57].
assert (* AndElim *) ((euclidean__axioms.BetS B Q C) /\ (euclidean__axioms.BetS P A Q)) as H58.
------------------------------------------------------------- exact H57.
------------------------------------------------------------- destruct H58 as [H58 H59].
assert (* Cut *) (euclidean__axioms.Col B C Q) as H60.
-------------------------------------------------------------- right.
right.
right.
right.
right.
exact H58.
-------------------------------------------------------------- assert (* Cut *) (~(G = Q)) as H61.
--------------------------------------------------------------- intro H61.
assert (* Cut *) (euclidean__axioms.BetS B G C) as H62.
---------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun G0: euclidean__axioms.Point => (euclidean__defs.CongA G0 B J D E F) -> ((euclidean__defs.OS G0 C B A) -> ((euclidean__axioms.nCol B A G0) -> ((~(B = G0)) -> ((~(A = G0)) -> ((euclidean__defs.CongA D E F G0 B J) -> ((G0 = G0) -> ((euclidean__defs.Out B G0 G0) -> ((euclidean__defs.CongA D E F G0 B A) -> ((euclidean__axioms.nCol G0 B A) -> ((~(euclidean__axioms.Col A B G0)) -> ((euclidean__defs.CongA G0 B A D E F) -> ((euclidean__defs.CongA A B G0 G0 B A) -> ((euclidean__defs.CongA A B G0 D E F) -> ((~(euclidean__axioms.Col A B G0)) -> ((~(G0 = A)) -> ((euclidean__axioms.BetS G0 A P) -> ((euclidean__axioms.Cong A P G0 A) -> ((~(euclidean__axioms.Col B A G0)) -> ((euclidean__defs.OS C G0 B A) -> ((euclidean__axioms.TS G0 B A P) -> ((~(euclidean__axioms.TS G0 B C A)) -> (euclidean__axioms.BetS B G0 C)))))))))))))))))))))))) with (x := G).
-----------------------------------------------------------------intro H62.
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
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
exact H58.

----------------------------------------------------------------- exact H61.
----------------------------------------------------------------- exact H11.
----------------------------------------------------------------- exact H12.
----------------------------------------------------------------- exact H13.
----------------------------------------------------------------- exact H14.
----------------------------------------------------------------- exact H15.
----------------------------------------------------------------- exact H16.
----------------------------------------------------------------- exact H18.
----------------------------------------------------------------- exact H19.
----------------------------------------------------------------- exact H20.
----------------------------------------------------------------- exact H21.
----------------------------------------------------------------- exact H22.
----------------------------------------------------------------- exact H23.
----------------------------------------------------------------- exact H24.
----------------------------------------------------------------- exact H25.
----------------------------------------------------------------- exact H26.
----------------------------------------------------------------- exact H27.
----------------------------------------------------------------- exact H30.
----------------------------------------------------------------- exact H31.
----------------------------------------------------------------- exact H34.
----------------------------------------------------------------- exact H35.
----------------------------------------------------------------- exact H36.
----------------------------------------------------------------- exact H47.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C G) as H63.
----------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (G)).
------------------------------------------------------------------left.
exact H62.

------------------------------------------------------------------ exact H4.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H64.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------------------------------------------------------right.
left.
exact H32.

------------------------------------------------------------------- exact H3.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B G G) as H65.
------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun G0: euclidean__axioms.Point => (euclidean__defs.CongA G0 B J D E F) -> ((euclidean__defs.OS G0 C B A) -> ((euclidean__axioms.nCol B A G0) -> ((~(B = G0)) -> ((~(A = G0)) -> ((euclidean__defs.CongA D E F G0 B J) -> ((G0 = G0) -> ((euclidean__defs.Out B G0 G0) -> ((euclidean__defs.CongA D E F G0 B A) -> ((euclidean__axioms.nCol G0 B A) -> ((~(euclidean__axioms.Col A B G0)) -> ((euclidean__defs.CongA G0 B A D E F) -> ((euclidean__defs.CongA A B G0 G0 B A) -> ((euclidean__defs.CongA A B G0 D E F) -> ((~(euclidean__axioms.Col A B G0)) -> ((~(G0 = A)) -> ((euclidean__axioms.BetS G0 A P) -> ((euclidean__axioms.Cong A P G0 A) -> ((~(euclidean__axioms.Col B A G0)) -> ((euclidean__defs.OS C G0 B A) -> ((euclidean__axioms.TS G0 B A P) -> ((~(euclidean__axioms.TS G0 B C A)) -> ((euclidean__axioms.BetS B G0 C) -> ((euclidean__defs.Out B C G0) -> (euclidean__defs.Out B G0 G0)))))))))))))))))))))))))) with (x := G).
--------------------------------------------------------------------intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
exact H72.

-------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------- exact H12.
-------------------------------------------------------------------- exact H13.
-------------------------------------------------------------------- exact H14.
-------------------------------------------------------------------- exact H15.
-------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------- exact H18.
-------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------- exact H20.
-------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------- exact H25.
-------------------------------------------------------------------- exact H26.
-------------------------------------------------------------------- exact H27.
-------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------- exact H31.
-------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------- exact H62.
-------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H66.
-------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) G).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B G B G) as H67.
--------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) G).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H68.
---------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) A).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B G A B C) as H69.
----------------------------------------------------------------------- exists A.
exists G.
exists A.
exists G.
split.
------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H65.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B G) as H70.
------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (A) (B) (C) H69).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C D E F) as H71.
------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (A) (B) (G) (D) (E) (F) (H70) H25).
------------------------------------------------------------------------- apply (@H1 H71).
--------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C G)) as H62.
---------------------------------------------------------------- intro H62.
assert (* Cut *) (euclidean__axioms.BetS P A G) as H63.
----------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (P) H30).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A G Q) as H64.
------------------------------------------------------------------ exists P.
split.
------------------------------------------------------------------- exact H59.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A G Q) as H65.
------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (A) (G) (Q) H64).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C B) as H66.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B))))) as H66.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (Q) H60).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B))))) as H67.
---------------------------------------------------------------------- exact H66.
---------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B)))) as H69.
----------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B))) as H71.
------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B)) as H73.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H74.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H67.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H67.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (G) H62).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H68.
----------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)))) as H70.
------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))) as H72.
------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)) as H74.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- destruct H74 as [H74 H75].
exact H68.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B Q) as H68.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))))) as H68.
----------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (C) (B) H66).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))))) as H69.
------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q)))) as H71.
------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))) as H73.
-------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q)) as H75.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H71.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H69.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G))) as H69.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (G) H63).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G))) as H70.
------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G)) as H72.
-------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------- destruct H72 as [H72 H73].
exact H4.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H70.
------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H69).
------------------------------------------------------------------------ assert (* Cut *) (B = B) as H71.
------------------------------------------------------------------------- apply (@logic.eq__refl (Point) B).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B B) as H72.
-------------------------------------------------------------------------- right.
right.
left.
exact H71.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G Q B) as H73.
--------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (Q) (B)).
----------------------------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False (G) (Q) (B) (H73)).
-----------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (C) (B) (G) (Q) (B) (H70) (H67) (H68) H72).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q G B) as H74.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q G B) /\ ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B G Q) /\ ((euclidean__axioms.Col G B Q) /\ (euclidean__axioms.Col B Q G))))) as H74.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (Q) (B) H73).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q G B) /\ ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B G Q) /\ ((euclidean__axioms.Col G B Q) /\ (euclidean__axioms.Col B Q G))))) as H75.
------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B G Q) /\ ((euclidean__axioms.Col G B Q) /\ (euclidean__axioms.Col B Q G)))) as H77.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col B G Q) /\ ((euclidean__axioms.Col G B Q) /\ (euclidean__axioms.Col B Q G))) as H79.
-------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col G B Q) /\ (euclidean__axioms.Col B Q G)) as H81.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H75.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q G A) as H75.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A Q) /\ ((euclidean__axioms.Col G Q A) /\ ((euclidean__axioms.Col Q A G) /\ ((euclidean__axioms.Col A Q G) /\ (euclidean__axioms.Col Q G A))))) as H75.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (Q) H65).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G A Q) /\ ((euclidean__axioms.Col G Q A) /\ ((euclidean__axioms.Col Q A G) /\ ((euclidean__axioms.Col A Q G) /\ (euclidean__axioms.Col Q G A))))) as H76.
------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col G Q A) /\ ((euclidean__axioms.Col Q A G) /\ ((euclidean__axioms.Col A Q G) /\ (euclidean__axioms.Col Q G A)))) as H78.
-------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col Q A G) /\ ((euclidean__axioms.Col A Q G) /\ (euclidean__axioms.Col Q G A))) as H80.
--------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A Q G) /\ (euclidean__axioms.Col Q G A)) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H83.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q G) as H76.
------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (Q) H61).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G B A) as H77.
------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (B) (A)).
--------------------------------------------------------------------------------intro H77.
apply (@euclidean__tactics.Col__nCol__False (G) (B) (A) (H77)).
---------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (G) (B) (A) (H74) (H75) H76).


------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H78.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H78.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (B) (A) H77).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H79.
---------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)))) as H81.
----------------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))) as H83.
------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)) as H85.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H86.
-------------------------------------------------------------------------------- apply (@H5).
---------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------------------------------intro H79.
apply (@H22 H78).


---------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A Q G)) as H63.
----------------------------------------------------------------- intro H63.
assert (* Cut *) (euclidean__axioms.BetS G Q A) as H64.
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (Q) (G) H63).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS G B C A) as H65.
------------------------------------------------------------------- exists Q.
split.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H60.
--------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (C) (G) H62).
------------------------------------------------------------------- apply (@H5).
--------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------------------------------------------------intro H66.
apply (@H47 H65).


----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C Q) as H64.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (C) (Q)).
-------------------------------------------------------------------left.
exact H58.

------------------------------------------------------------------- exact H4.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H65.
------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
--------------------------------------------------------------------right.
left.
exact H32.

-------------------------------------------------------------------- exact H3.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A G Q)) as H66.
-------------------------------------------------------------------- intro H66.
assert (* Cut *) (euclidean__defs.CongA A B G A B G) as H67.
--------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (G)).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).

--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B G A B C) as H68.
---------------------------------------------------------------------- exists A.
exists G.
exists Q.
split.
----------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------- split.
------------------------------------------------------------------------ exact H65.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------- exact H67.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H69.
----------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA D E F A B C) as H70.
------------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (G) (A) (B) (C) (D) (E) (F) (H68) H69).
------------------------------------------------------------------------ apply (@H2 H70).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P A G) as H67.
--------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (P) H30).
--------------------------------------------------------------------- assert (* Cut *) (G = Q) as H68.
---------------------------------------------------------------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity (P) (A) (G) (Q) (H67) (H59) (H66) H63).
---------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H69.
----------------------------------------------------------------------- intro H69.
apply (@H5).
------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------------------------------------------------------------------intro H70.
apply (@H61 H68).


----------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
------------------------------------------------------------------------intro H70.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H71.
------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H73.
-------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H75.
--------------------------------------------------------------------------- exact H13.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H77.
---------------------------------------------------------------------------- exact H21.
---------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H79.
----------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H81.
------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H83.
------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H85.
-------------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H87.
--------------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H89.
---------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H91.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H93.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H95.
------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H97.
-------------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H99.
--------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H101.
---------------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H103.
----------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H105.
------------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H107.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H109.
-------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H111.
--------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H113.
---------------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H115.
----------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H117.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H117 as [H117 H118].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H119.
------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* Cut *) (False) as H121.
-------------------------------------------------------------------------------------------------- apply (@H61 H68).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H122.
--------------------------------------------------------------------------------------------------- apply (@H69 H70).
--------------------------------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------------------------------exact H122.
---------------------------------------------------------------------------------------------------- contradiction.

--------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.LtA A B C D E F))) as H55.
---------------------------------------------------------- intro H55.
assert (* Cut *) (euclidean__axioms.BetS P A G) as H56.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (P) H30).
----------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col P G B)) as H57.
------------------------------------------------------------ intro H57.
assert (* Cut *) (euclidean__axioms.Col P A G) as H58.
------------------------------------------------------------- right.
right.
right.
right.
left.
exact H56.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P G A) as H59.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))))) as H59.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (G) H58).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P G) /\ ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))))) as H60.
---------------------------------------------------------------- exact H59.
---------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col A G P) /\ ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P)))) as H62.
----------------------------------------------------------------- exact H61.
----------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col G P A) /\ ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P))) as H64.
------------------------------------------------------------------ exact H63.
------------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col P G A) /\ (euclidean__axioms.Col G A P)) as H66.
------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H66.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P G) as H60.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G))) as H60.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (A) (G) H56).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G))) as H61.
----------------------------------------------------------------- exact H60.
----------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P G)) as H63.
------------------------------------------------------------------ exact H62.
------------------------------------------------------------------ destruct H63 as [H63 H64].
exact H64.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H61.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (B) (A)).
-----------------------------------------------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False (G) (B) (A) (H61)).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (G) (B) (A) (H57) (H59) H60).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H62.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H62.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (B) (A) H61).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H63.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)))) as H65.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))) as H67.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)) as H69.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H70.
----------------------------------------------------------------- apply (@H5).
------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------------------------------------------------------------intro H63.
apply (@H22 H62).


------------------------------------------------------------ assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS B Q G) /\ (euclidean__axioms.BetS P R Q)) as H58.
------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (B) (P) (A) (R) (G) (H54) (H56)).
--------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (P) (G) (B) H57).

------------------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS B Q G) /\ (euclidean__axioms.BetS P R Q))) as H59.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H59 as [Q H59].
assert (* AndElim *) ((euclidean__axioms.BetS B Q G) /\ (euclidean__axioms.BetS P R Q)) as H60.
--------------------------------------------------------------- exact H59.
--------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* Cut *) (euclidean__axioms.neq Q G) as H62.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H62.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H60).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H63.
------------------------------------------------------------------ exact H62.
------------------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H65.
------------------------------------------------------------------- exact H64.
------------------------------------------------------------------- destruct H65 as [H65 H66].
exact H63.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H63.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H63.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (Q) (G) H60).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G))) as H64.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B G)) as H66.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H66.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H64.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------------------------------------------------------right.
left.
exact H32.

------------------------------------------------------------------- exact H3.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B G Q) as H65.
------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (G) (Q)).
--------------------------------------------------------------------left.
exact H60.

-------------------------------------------------------------------- exact H14.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q G) as H66.
-------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (G)).
---------------------------------------------------------------------right.
right.
exact H60.

--------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS R C Q)) as H67.
--------------------------------------------------------------------- intro H67.
assert (* Cut *) (euclidean__defs.Out B A R) as H68.
---------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (R)).
-----------------------------------------------------------------------left.
exact H54.

----------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G Q) as H69.
----------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H70.
------------------------------------------------------------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA A B C A B G) as H71.
------------------------------------------------------------------------- exists R.
exists C.
exists Q.
split.
-------------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H72.
-------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C D E F) as H73.
--------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (A) (B) (G) (D) (E) (F) (H71) H72).
--------------------------------------------------------------------------- apply (@H5).
----------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-----------------------------------------------------------------------------intro H74.
apply (@H55 H73).


--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS R Q C)) as H68.
---------------------------------------------------------------------- intro H68.
assert (* Cut *) (A = A) as H69.
----------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H70.
------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B Q G) as H71.
------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------- assert (* Cut *) (G = G) as H72.
-------------------------------------------------------------------------- exact H18.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G G) as H73.
--------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H74.
---------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) A).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B G B G) as H75.
----------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) G).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H76.
------------------------------------------------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) G).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B G A B Q) as H77.
------------------------------------------------------------------------------- exists A.
exists G.
exists A.
exists G.
split.
-------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A R) as H78.
-------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (R)).
---------------------------------------------------------------------------------left.
exact H54.

--------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------- assert (* Cut *) (C = C) as H79.
--------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) C).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H80.
---------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
-----------------------------------------------------------------------------------right.
left.
exact H79.

----------------------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B G A B C) as H81.
----------------------------------------------------------------------------------- exists R.
exists Q.
exists C.
split.
------------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B G) as H82.
------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (G) (D) (E) (F) H25).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA D E F A B C) as H83.
------------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (G) (A) (B) (C) (D) (E) (F) (H81) H82).
------------------------------------------------------------------------------------- apply (@H2 H83).
---------------------------------------------------------------------- assert (* Cut *) (Q = C) as H69.
----------------------------------------------------------------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity (P) (R) (Q) (C) (H61) (H44) (H68) H67).
----------------------------------------------------------------------- assert (* Cut *) (C = C) as H70.
------------------------------------------------------------------------ apply (@logic.eq__refl (Point) C).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C C) as H71.
------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
--------------------------------------------------------------------------right.
left.
exact H70.

-------------------------------------------------------------------------- exact H4.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C G) as H72.
-------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> (euclidean__defs.Out B C0 G))))))))))))))))))) with (y := C).
---------------------------------------------------------------------------intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
assert (* Cut *) (Q = Q) as H89.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- exact H66.

--------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------------- exact H5.
--------------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------------- exact H40.
--------------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------------- exact H44.
--------------------------------------------------------------------------- exact H47.
--------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------- assert (* Cut *) (A = A) as H73.
--------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((euclidean__defs.Out B C0 G) -> (A = A)))))))))))))))))))) with (y := C).
----------------------------------------------------------------------------intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
assert (* Cut *) (Q = Q) as H91.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- exact H32.

---------------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------------- exact H.
---------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------------- exact H5.
---------------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------------- exact H35.
---------------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------------- exact H43.
---------------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------------- exact H47.
---------------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------------- exact H67.
---------------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H74.
---------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((euclidean__defs.Out B C0 G) -> (euclidean__defs.Out B A A)))))))))))))))))))) with (y := C).
-----------------------------------------------------------------------------intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
assert (* Cut *) (Q = Q) as H92.
------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------ exact H64.

----------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------- exact H2.
----------------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------------- exact H37.
----------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q G) as H75.
----------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((euclidean__defs.Out B C0 G) -> (euclidean__defs.Out B Q G)))))))))))))))))))) with (y := C).
------------------------------------------------------------------------------intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
assert (* Cut *) (Q = Q) as H93.
------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------- exact H92.

------------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------------ exact H.
------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------ exact H5.
------------------------------------------------------------------------------ exact H12.
------------------------------------------------------------------------------ exact H35.
------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------ exact H44.
------------------------------------------------------------------------------ exact H47.
------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------ exact H72.
----------------------------------------------------------------------------- assert (* Cut *) (G = G) as H76.
------------------------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((euclidean__defs.Out B C0 G) -> (G = G)))))))))))))))))))) with (y := C).
-------------------------------------------------------------------------------intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
assert (* Cut *) (Q = Q) as H94.
-------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------- exact H18.

------------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------- exact H4.
------------------------------------------------------------------------------- exact H5.
------------------------------------------------------------------------------- exact H12.
------------------------------------------------------------------------------- exact H35.
------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------- exact H40.
------------------------------------------------------------------------------- exact H43.
------------------------------------------------------------------------------- exact H44.
------------------------------------------------------------------------------- exact H47.
------------------------------------------------------------------------------- exact H55.
------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B G G) as H77.
------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun C0: euclidean__axioms.Point => (euclidean__axioms.nCol A B C0) -> ((~(euclidean__defs.CongA A B C0 D E F)) -> ((~(euclidean__defs.LtA D E F A B C0)) -> ((~(B = C0)) -> ((~(euclidean__axioms.Col B A C0)) -> ((euclidean__defs.OS G C0 B A) -> ((euclidean__defs.OS C0 G B A) -> ((euclidean__axioms.TS C0 B A P) -> ((euclidean__axioms.BetS C0 R P) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.BetS P R C0) -> ((~(euclidean__axioms.TS G B C0 A)) -> ((~(euclidean__defs.LtA A B C0 D E F)) -> ((~(euclidean__axioms.BetS R C0 Q)) -> ((~(euclidean__axioms.BetS R Q C0)) -> ((C0 = C0) -> ((euclidean__defs.Out B C0 C0) -> ((euclidean__defs.Out B C0 G) -> (euclidean__defs.Out B G G)))))))))))))))))))) with (y := C).
--------------------------------------------------------------------------------intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
assert (* Cut *) (Q = Q) as H95.
--------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------- exact H19.

-------------------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------------------- exact H.
-------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------------------- exact H4.
-------------------------------------------------------------------------------- exact H5.
-------------------------------------------------------------------------------- exact H12.
-------------------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------------- exact H44.
-------------------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H78.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) A).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B G B G) as H79.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) G).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H80.
---------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) G).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B G A B Q) as H81.
----------------------------------------------------------------------------------- exists A.
exists G.
exists A.
exists G.
split.
------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (A) (B) (G) H26).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B G) as H82.
------------------------------------------------------------------------------------ exists A.
exists G.
exists A.
exists G.
split.
------------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C D E F) as H83.
------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (A) (B) (G) (D) (E) (F) (H82) H25).
------------------------------------------------------------------------------------- apply (@H1 H83).
---------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.LtA A B C D E F)).
-----------------------------------------------------------intro H56.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H57.
------------------------------------------------------------ exact H.
------------------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))))) as H59.
------------------------------------------------------------- exact H0.
------------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))))) as H61.
-------------------------------------------------------------- exact H13.
-------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))))) as H63.
--------------------------------------------------------------- exact H21.
--------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H65.
---------------------------------------------------------------- exact H43.
---------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H67.
----------------------------------------------------------------- exact H58.
----------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))))) as H69.
------------------------------------------------------------------ exact H60.
------------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))))) as H71.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))))) as H73.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H75.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H77.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))))) as H79.
----------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))))) as H81.
------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))))) as H83.
------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H85.
-------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H87.
--------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E F)) /\ ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F)))) as H89.
---------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A G)) /\ ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G)))) as H91.
----------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS G B A)) /\ ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A)))) as H93.
------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H95.
------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H97.
-------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((~(euclidean__axioms.BetS D F E)) /\ (~(euclidean__axioms.BetS E D F))) as H99.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS B G A)) /\ (~(euclidean__axioms.BetS A B G))) as H101.
---------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__axioms.BetS G A B)) /\ (~(euclidean__axioms.BetS B G A))) as H103.
----------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H105.
------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* Cut *) (False) as H107.
------------------------------------------------------------------------------------- apply (@H55 H56).
------------------------------------------------------------------------------------- assert False.
--------------------------------------------------------------------------------------exact H107.
-------------------------------------------------------------------------------------- contradiction.

--------------------------------------------- exact H49.
-------------------------------------- exact H45.
Qed.
