Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__9__5a : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.TS P A B C) -> ((euclidean__axioms.BetS R P Q) -> ((euclidean__axioms.nCol R Q C) -> ((euclidean__axioms.Col A B R) -> (euclidean__axioms.TS Q A B C)))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro Q.
intro R.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS P S C) /\ ((euclidean__axioms.Col A B S) /\ (euclidean__axioms.nCol A B P))) as H3.
- exact H.
- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS P S C) /\ ((euclidean__axioms.Col A B S) /\ (euclidean__axioms.nCol A B P)))) as H4.
-- exact H3.
-- destruct H4 as [S H4].
assert (* AndElim *) ((euclidean__axioms.BetS P S C) /\ ((euclidean__axioms.Col A B S) /\ (euclidean__axioms.nCol A B P))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col A B S) /\ (euclidean__axioms.nCol A B P)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.BetS C S P) as H9.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (S) (C) H5).
----- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS C F Q) /\ (euclidean__axioms.BetS R S F)) as H10.
------ apply (@euclidean__axioms.postulate__Pasch__outer (C) (R) (P) (S) (Q) (H9) (H0) H1).
------ assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS C F Q) /\ (euclidean__axioms.BetS R S F))) as H11.
------- exact H10.
------- destruct H11 as [F H11].
assert (* AndElim *) ((euclidean__axioms.BetS C F Q) /\ (euclidean__axioms.BetS R S F)) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* Cut *) (euclidean__axioms.Col R S F) as H14.
--------- right.
right.
right.
right.
left.
exact H13.
--------- assert (* Cut *) (~(A = B)) as H15.
---------- intro H15.
assert (* Cut *) (euclidean__axioms.Col A B P) as H16.
----------- left.
exact H15.
----------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H8) H16).
---------- assert (* Cut *) (euclidean__axioms.neq B A) as H16.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H15).
----------- assert (* Cut *) (euclidean__axioms.Col B R S) as H17.
------------ apply (@euclidean__tactics.not__nCol__Col (B) (R) (S)).
-------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (B) (R) (S) (H17)).
--------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (R) (S) (H2) (H7) H15).


------------ assert (* Cut *) (euclidean__axioms.Col R S B) as H18.
------------- assert (* Cut *) ((euclidean__axioms.Col R B S) /\ ((euclidean__axioms.Col R S B) /\ ((euclidean__axioms.Col S B R) /\ ((euclidean__axioms.Col B S R) /\ (euclidean__axioms.Col S R B))))) as H18.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (R) (S) H17).
-------------- assert (* AndElim *) ((euclidean__axioms.Col R B S) /\ ((euclidean__axioms.Col R S B) /\ ((euclidean__axioms.Col S B R) /\ ((euclidean__axioms.Col B S R) /\ (euclidean__axioms.Col S R B))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col R S B) /\ ((euclidean__axioms.Col S B R) /\ ((euclidean__axioms.Col B S R) /\ (euclidean__axioms.Col S R B)))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col S B R) /\ ((euclidean__axioms.Col B S R) /\ (euclidean__axioms.Col S R B))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col B S R) /\ (euclidean__axioms.Col S R B)) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
exact H21.
------------- assert (* Cut *) (euclidean__axioms.neq R S) as H19.
-------------- assert (* Cut *) ((euclidean__axioms.neq S F) /\ ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F))) as H19.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal (R) (S) (F) H13).
--------------- assert (* AndElim *) ((euclidean__axioms.neq S F) /\ ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F)) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
exact H22.
-------------- assert (* Cut *) (euclidean__axioms.Col S F B) as H20.
--------------- apply (@euclidean__tactics.not__nCol__Col (S) (F) (B)).
----------------intro H20.
apply (@euclidean__tactics.Col__nCol__False (S) (F) (B) (H20)).
-----------------apply (@lemma__collinear4.lemma__collinear4 (R) (S) (F) (B) (H14) (H18) H19).


--------------- assert (* Cut *) (euclidean__axioms.Col S B A) as H21.
---------------- assert (* Cut *) ((euclidean__axioms.Col B A S) /\ ((euclidean__axioms.Col B S A) /\ ((euclidean__axioms.Col S A B) /\ ((euclidean__axioms.Col A S B) /\ (euclidean__axioms.Col S B A))))) as H21.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (S) H7).
----------------- assert (* AndElim *) ((euclidean__axioms.Col B A S) /\ ((euclidean__axioms.Col B S A) /\ ((euclidean__axioms.Col S A B) /\ ((euclidean__axioms.Col A S B) /\ (euclidean__axioms.Col S B A))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B S A) /\ ((euclidean__axioms.Col S A B) /\ ((euclidean__axioms.Col A S B) /\ (euclidean__axioms.Col S B A)))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col S A B) /\ ((euclidean__axioms.Col A S B) /\ (euclidean__axioms.Col S B A))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col A S B) /\ (euclidean__axioms.Col S B A)) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
exact H29.
---------------- assert (* Cut *) (euclidean__axioms.Col S B F) as H22.
----------------- assert (* Cut *) ((euclidean__axioms.Col F S B) /\ ((euclidean__axioms.Col F B S) /\ ((euclidean__axioms.Col B S F) /\ ((euclidean__axioms.Col S B F) /\ (euclidean__axioms.Col B F S))))) as H22.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (S) (F) (B) H20).
------------------ assert (* AndElim *) ((euclidean__axioms.Col F S B) /\ ((euclidean__axioms.Col F B S) /\ ((euclidean__axioms.Col B S F) /\ ((euclidean__axioms.Col S B F) /\ (euclidean__axioms.Col B F S))))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col F B S) /\ ((euclidean__axioms.Col B S F) /\ ((euclidean__axioms.Col S B F) /\ (euclidean__axioms.Col B F S)))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col B S F) /\ ((euclidean__axioms.Col S B F) /\ (euclidean__axioms.Col B F S))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col S B F) /\ (euclidean__axioms.Col B F S)) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
exact H29.
----------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H23.
------------------ assert (* Cut *) ((S = B) \/ (euclidean__axioms.neq S B)) as H23.
------------------- apply (@euclidean__tactics.eq__or__neq (S) B).
------------------- assert (* Cut *) ((S = B) \/ (euclidean__axioms.neq S B)) as H24.
-------------------- exact H23.
-------------------- assert (* Cut *) ((S = B) \/ (euclidean__axioms.neq S B)) as __TmpHyp.
--------------------- exact H24.
--------------------- assert (S = B \/ euclidean__axioms.neq S B) as H25.
---------------------- exact __TmpHyp.
---------------------- destruct H25 as [H25|H25].
----------------------- assert (* Cut *) (euclidean__axioms.Col B A S) as H26.
------------------------ assert (* Cut *) ((euclidean__axioms.Col B S A) /\ ((euclidean__axioms.Col B A S) /\ ((euclidean__axioms.Col A S B) /\ ((euclidean__axioms.Col S A B) /\ (euclidean__axioms.Col A B S))))) as H26.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (S) (B) (A) H21).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col B S A) /\ ((euclidean__axioms.Col B A S) /\ ((euclidean__axioms.Col A S B) /\ ((euclidean__axioms.Col S A B) /\ (euclidean__axioms.Col A B S))))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B A S) /\ ((euclidean__axioms.Col A S B) /\ ((euclidean__axioms.Col S A B) /\ (euclidean__axioms.Col A B S)))) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col A S B) /\ ((euclidean__axioms.Col S A B) /\ (euclidean__axioms.Col A B S))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col S A B) /\ (euclidean__axioms.Col A B S)) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
exact H29.
------------------------ assert (* Cut *) (euclidean__axioms.Col R S F) as H27.
------------------------- exact H14.
------------------------- assert (* Cut *) (euclidean__axioms.Col R B F) as H28.
-------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun S0: euclidean__axioms.Point => (euclidean__axioms.BetS P S0 C) -> ((euclidean__axioms.Col A B S0) -> ((euclidean__axioms.BetS C S0 P) -> ((euclidean__axioms.BetS R S0 F) -> ((euclidean__axioms.Col R S0 F) -> ((euclidean__axioms.Col B R S0) -> ((euclidean__axioms.Col R S0 B) -> ((euclidean__axioms.neq R S0) -> ((euclidean__axioms.Col S0 F B) -> ((euclidean__axioms.Col S0 B A) -> ((euclidean__axioms.Col S0 B F) -> ((euclidean__axioms.Col B A S0) -> ((euclidean__axioms.Col R S0 F) -> (euclidean__axioms.Col R B F))))))))))))))) with (x := S).
---------------------------intro H28.
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
exact H40.

--------------------------- exact H25.
--------------------------- exact H5.
--------------------------- exact H7.
--------------------------- exact H9.
--------------------------- exact H13.
--------------------------- exact H14.
--------------------------- exact H17.
--------------------------- exact H18.
--------------------------- exact H19.
--------------------------- exact H20.
--------------------------- exact H21.
--------------------------- exact H22.
--------------------------- exact H26.
--------------------------- exact H27.
-------------------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H29.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H29.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (R) H2).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
exact H37.
--------------------------- assert (* Cut *) (~(R = B)) as H30.
---------------------------- intro H30.
assert (* Cut *) (R = S) as H31.
----------------------------- apply (@logic.eq__trans (Point) (R) (B) (S) (H30)).
------------------------------apply (@logic.eq__sym (Point) (S) (B) H25).

----------------------------- assert (* Cut *) (euclidean__axioms.neq R S) as H32.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq S F) /\ ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F))) as H32.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (R) (S) (F) H13).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq S F) /\ ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq R S) /\ (euclidean__axioms.neq R F)) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
exact H19.
------------------------------ assert (* Cut *) (euclidean__axioms.neq R B) as H33.
------------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS R0 P Q) -> ((euclidean__axioms.nCol R0 Q C) -> ((euclidean__axioms.Col A B R0) -> ((euclidean__axioms.BetS R0 S F) -> ((euclidean__axioms.Col R0 S F) -> ((euclidean__axioms.Col B R0 S) -> ((euclidean__axioms.Col R0 S B) -> ((euclidean__axioms.neq R0 S) -> ((euclidean__axioms.Col R0 S F) -> ((euclidean__axioms.Col R0 B F) -> ((euclidean__axioms.Col R0 B A) -> ((R0 = S) -> ((euclidean__axioms.neq R0 S) -> (euclidean__axioms.neq R0 B))))))))))))))) with (x := R).
--------------------------------intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
apply (@eq__ind__r euclidean__axioms.Point B (fun S0: euclidean__axioms.Point => (euclidean__axioms.BetS P S0 C) -> ((euclidean__axioms.Col A B S0) -> ((euclidean__axioms.BetS C S0 P) -> ((euclidean__axioms.Col B S0 F) -> ((euclidean__axioms.BetS B S0 F) -> ((euclidean__axioms.neq B S0) -> ((euclidean__axioms.Col B S0 B) -> ((euclidean__axioms.Col B B S0) -> ((euclidean__axioms.Col S0 F B) -> ((euclidean__axioms.Col S0 B A) -> ((euclidean__axioms.Col S0 B F) -> ((euclidean__axioms.Col B A S0) -> ((euclidean__axioms.Col B S0 F) -> ((euclidean__axioms.neq B S0) -> ((B = S0) -> (euclidean__axioms.neq B B))))))))))))))))) with (x := S).
---------------------------------intro H46.
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
intro H58.
intro H59.
intro H60.
exact H59.

--------------------------------- exact H25.
--------------------------------- exact H5.
--------------------------------- exact H7.
--------------------------------- exact H9.
--------------------------------- exact H37.
--------------------------------- exact H36.
--------------------------------- exact H40.
--------------------------------- exact H39.
--------------------------------- exact H38.
--------------------------------- exact H20.
--------------------------------- exact H21.
--------------------------------- exact H22.
--------------------------------- exact H26.
--------------------------------- exact H41.
--------------------------------- exact H45.
--------------------------------- exact H44.

-------------------------------- exact H30.
-------------------------------- exact H0.
-------------------------------- exact H1.
-------------------------------- exact H2.
-------------------------------- exact H13.
-------------------------------- exact H14.
-------------------------------- exact H17.
-------------------------------- exact H18.
-------------------------------- exact H19.
-------------------------------- exact H27.
-------------------------------- exact H28.
-------------------------------- exact H29.
-------------------------------- exact H31.
-------------------------------- exact H32.
------------------------------- apply (@H19 H31).
---------------------------- assert (* Cut *) (euclidean__axioms.Col B F A) as H31.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (A)).
------------------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (A) (H31)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (R) (B) (F) (A) (H28) (H29) H30).


----------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H32.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))))) as H32.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (A) H31).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B)))) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
exact H37.
------------------------------ exact H32.
----------------------- assert (* Cut *) (euclidean__axioms.Col B A F) as H26.
------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (A) (F)).
-------------------------intro H26.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (F) (H26)).
--------------------------apply (@lemma__collinear4.lemma__collinear4 (S) (B) (A) (F) (H21) (H22) H25).


------------------------ assert (* Cut *) (euclidean__axioms.Col A B F) as H27.
------------------------- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H27.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (F) H26).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)))) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
exact H28.
------------------------- exact H27.
------------------ assert (* Cut *) (~(euclidean__axioms.Col A B Q)) as H24.
------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col B Q R) as H25.
-------------------- apply (@euclidean__tactics.not__nCol__Col (B) (Q) (R)).
---------------------intro H25.
apply (@euclidean__tactics.Col__nCol__False (B) (Q) (R) (H25)).
----------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (Q) (R) (H24) (H2) H15).


-------------------- assert (* Cut *) (euclidean__axioms.Col B R Q) as H26.
--------------------- assert (* Cut *) ((euclidean__axioms.Col Q B R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))))) as H26.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (R) H25).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col Q B R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H33.
--------------------- assert (* Cut *) (euclidean__axioms.Col B R F) as H27.
---------------------- apply (@euclidean__tactics.not__nCol__Col (B) (R) (F)).
-----------------------intro H27.
apply (@euclidean__tactics.Col__nCol__False (B) (R) (F) (H27)).
------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (R) (F) (H2) (H23) H15).


---------------------- assert (* Cut *) (euclidean__axioms.Col R Q F) as H28.
----------------------- assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as H28.
------------------------ apply (@euclidean__tactics.eq__or__neq (B) R).
------------------------ assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as H29.
------------------------- exact H28.
------------------------- assert (* Cut *) ((B = R) \/ (euclidean__axioms.neq B R)) as __TmpHyp.
-------------------------- exact H29.
-------------------------- assert (B = R \/ euclidean__axioms.neq B R) as H30.
--------------------------- exact __TmpHyp.
--------------------------- destruct H30 as [H30|H30].
---------------------------- assert (* Cut *) (~(A = R)) as H31.
----------------------------- intro H31.
assert (* Cut *) (A = B) as H32.
------------------------------ apply (@logic.eq__trans (Point) (A) (R) (B) (H31)).
-------------------------------apply (@logic.eq__sym (Point) (B) (R) H30).

------------------------------ apply (@H15 H32).
----------------------------- assert (* Cut *) (euclidean__axioms.Col B A R) as H32.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H32.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (R) H2).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)))) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
exact H33.
------------------------------ assert (* Cut *) (euclidean__axioms.Col B A F) as H33.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H33.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H23).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
exact H34.
------------------------------- assert (* Cut *) (euclidean__axioms.Col A R F) as H34.
-------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun B0: euclidean__axioms.Point => (euclidean__axioms.TS P A B0 C) -> ((euclidean__axioms.Col A B0 R) -> ((euclidean__axioms.Col A B0 S) -> ((euclidean__axioms.nCol A B0 P) -> ((~(A = B0)) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__axioms.Col B0 R S) -> ((euclidean__axioms.Col R S B0) -> ((euclidean__axioms.Col S F B0) -> ((euclidean__axioms.Col S B0 A) -> ((euclidean__axioms.Col S B0 F) -> ((euclidean__axioms.Col A B0 F) -> ((euclidean__axioms.Col A B0 Q) -> ((euclidean__axioms.Col B0 Q R) -> ((euclidean__axioms.Col B0 R Q) -> ((euclidean__axioms.Col B0 R F) -> ((euclidean__axioms.Col B0 A R) -> ((euclidean__axioms.Col B0 A F) -> (euclidean__axioms.Col A R F)))))))))))))))))))) with (x := B).
---------------------------------intro H34.
intro H35.
intro H36.
intro H37.
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
intro H49.
intro H50.
intro H51.
exact H45.

--------------------------------- exact H30.
--------------------------------- exact H.
--------------------------------- exact H2.
--------------------------------- exact H7.
--------------------------------- exact H8.
--------------------------------- exact H15.
--------------------------------- exact H16.
--------------------------------- exact H17.
--------------------------------- exact H18.
--------------------------------- exact H20.
--------------------------------- exact H21.
--------------------------------- exact H22.
--------------------------------- exact H23.
--------------------------------- exact H24.
--------------------------------- exact H25.
--------------------------------- exact H26.
--------------------------------- exact H27.
--------------------------------- exact H32.
--------------------------------- exact H33.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B A Q) as H35.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H35.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (Q) H24).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H36.
----------------------------------- exact H35.
----------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
exact H36.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A R) as H36.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B))))) as H36.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (Q) H35).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B))))) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B)))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
exact H32.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col A R Q) as H37.
----------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun B0: euclidean__axioms.Point => (euclidean__axioms.TS P A B0 C) -> ((euclidean__axioms.Col A B0 R) -> ((euclidean__axioms.Col A B0 S) -> ((euclidean__axioms.nCol A B0 P) -> ((~(A = B0)) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__axioms.Col B0 R S) -> ((euclidean__axioms.Col R S B0) -> ((euclidean__axioms.Col S F B0) -> ((euclidean__axioms.Col S B0 A) -> ((euclidean__axioms.Col S B0 F) -> ((euclidean__axioms.Col A B0 F) -> ((euclidean__axioms.Col A B0 Q) -> ((euclidean__axioms.Col B0 Q R) -> ((euclidean__axioms.Col B0 R Q) -> ((euclidean__axioms.Col B0 R F) -> ((euclidean__axioms.Col B0 A R) -> ((euclidean__axioms.Col B0 A F) -> ((euclidean__axioms.Col B0 A Q) -> ((euclidean__axioms.Col B0 A R) -> (euclidean__axioms.Col A R Q)))))))))))))))))))))) with (x := B).
------------------------------------intro H37.
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
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H49.

------------------------------------ exact H30.
------------------------------------ exact H.
------------------------------------ exact H2.
------------------------------------ exact H7.
------------------------------------ exact H8.
------------------------------------ exact H15.
------------------------------------ exact H16.
------------------------------------ exact H17.
------------------------------------ exact H18.
------------------------------------ exact H20.
------------------------------------ exact H21.
------------------------------------ exact H22.
------------------------------------ exact H23.
------------------------------------ exact H24.
------------------------------------ exact H25.
------------------------------------ exact H26.
------------------------------------ exact H27.
------------------------------------ exact H32.
------------------------------------ exact H33.
------------------------------------ exact H35.
------------------------------------ exact H36.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col R F Q) as H38.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (R) (F) (Q)).
-------------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (R) (F) (Q) (H38)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (R) (F) (Q) (H34) (H37) H31).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col R Q F) as H39.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col F Q R) /\ ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col R Q F) /\ (euclidean__axioms.Col Q F R))))) as H39.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (R) (F) (Q) H38).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col F Q R) /\ ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col R Q F) /\ (euclidean__axioms.Col Q F R))))) as H40.
--------------------------------------- exact H39.
--------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col F Q R) /\ ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col R Q F) /\ (euclidean__axioms.Col Q F R)))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col R Q F) /\ (euclidean__axioms.Col Q F R))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col R Q F) /\ (euclidean__axioms.Col Q F R)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
exact H46.
------------------------------------- exact H39.
---------------------------- assert (* Cut *) (euclidean__axioms.Col R Q F) as H31.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (R) (Q) (F)).
------------------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False (R) (Q) (F) (H31)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (R) (Q) (F) (H26) (H27) H30).


----------------------------- exact H31.
----------------------- assert (* Cut *) (euclidean__axioms.Col F Q R) as H29.
------------------------ assert (* Cut *) ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col Q F R) /\ ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col R F Q) /\ (euclidean__axioms.Col F Q R))))) as H29.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (R) (Q) (F) H28).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q R F) /\ ((euclidean__axioms.Col Q F R) /\ ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col R F Q) /\ (euclidean__axioms.Col F Q R))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col Q F R) /\ ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col R F Q) /\ (euclidean__axioms.Col F Q R)))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col F R Q) /\ ((euclidean__axioms.Col R F Q) /\ (euclidean__axioms.Col F Q R))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col R F Q) /\ (euclidean__axioms.Col F Q R)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H37.
------------------------ assert (* Cut *) (euclidean__axioms.Col C F Q) as H30.
------------------------- right.
right.
right.
right.
left.
exact H12.
------------------------- assert (* Cut *) (euclidean__axioms.Col F Q C) as H31.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col F C Q) /\ ((euclidean__axioms.Col F Q C) /\ ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C Q F) /\ (euclidean__axioms.Col Q F C))))) as H31.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (Q) H30).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C Q) /\ ((euclidean__axioms.Col F Q C) /\ ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C Q F) /\ (euclidean__axioms.Col Q F C))))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col F Q C) /\ ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C Q F) /\ (euclidean__axioms.Col Q F C)))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C Q F) /\ (euclidean__axioms.Col Q F C))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C Q F) /\ (euclidean__axioms.Col Q F C)) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
exact H34.
-------------------------- assert (* Cut *) (euclidean__axioms.neq F Q) as H32.
--------------------------- assert (* Cut *) ((euclidean__axioms.neq F Q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C Q))) as H32.
---------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (Q) H12).
---------------------------- assert (* AndElim *) ((euclidean__axioms.neq F Q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C Q))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C Q)) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
exact H33.
--------------------------- assert (* Cut *) (euclidean__axioms.Col Q R C) as H33.
---------------------------- apply (@euclidean__tactics.not__nCol__Col (Q) (R) (C)).
-----------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (Q) (R) (C) (H33)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (Q) (R) (C) (H29) (H31) H32).


---------------------------- assert (* Cut *) (euclidean__axioms.Col R Q C) as H34.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col R Q C) /\ ((euclidean__axioms.Col R C Q) /\ ((euclidean__axioms.Col C Q R) /\ ((euclidean__axioms.Col Q C R) /\ (euclidean__axioms.Col C R Q))))) as H34.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (Q) (R) (C) H33).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col R Q C) /\ ((euclidean__axioms.Col R C Q) /\ ((euclidean__axioms.Col C Q R) /\ ((euclidean__axioms.Col Q C R) /\ (euclidean__axioms.Col C R Q))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col R C Q) /\ ((euclidean__axioms.Col C Q R) /\ ((euclidean__axioms.Col Q C R) /\ (euclidean__axioms.Col C R Q)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C Q R) /\ ((euclidean__axioms.Col Q C R) /\ (euclidean__axioms.Col C R Q))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col Q C R) /\ (euclidean__axioms.Col C R Q)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H35.
----------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H8)).
------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (P)).
-------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (R) (Q) (C) (H1) H34).


------------------- assert (* Cut *) (euclidean__axioms.BetS Q F C) as H25.
-------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (Q) H12).
-------------------- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H26.
--------------------- exists F.
split.
---------------------- exact H25.
---------------------- split.
----------------------- exact H23.
----------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (Q) H24).
--------------------- exact H26.
Qed.
