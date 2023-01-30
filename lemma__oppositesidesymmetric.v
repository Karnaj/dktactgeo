Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__oppositesidesymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__axioms.TS P A B Q) -> (euclidean__axioms.TS Q A B P).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro H.
assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS P R Q) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.nCol A B P))) as H0.
- exact H.
- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS P R Q) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.nCol A B P)))) as H1.
-- exact H0.
-- destruct H1 as [R H1].
assert (* AndElim *) ((euclidean__axioms.BetS P R Q) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.nCol A B P))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.nCol A B P)) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* Cut *) (~(A = B)) as H6.
----- intro H6.
assert (* Cut *) (euclidean__axioms.Col A B P) as H7.
------ left.
exact H6.
------ apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H5) H7).
----- assert (* Cut *) (euclidean__axioms.BetS Q R P) as H7.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (R) (Q) H2).
------ assert (* Cut *) (~(euclidean__axioms.Col A B Q)) as H8.
------- intro H8.
assert (* Cut *) (euclidean__axioms.Col P R Q) as H9.
-------- right.
right.
right.
right.
left.
exact H2.
-------- assert (* Cut *) (euclidean__axioms.Col B Q R) as H10.
--------- apply (@euclidean__tactics.not__nCol__Col (B) (Q) (R)).
----------intro H10.
apply (@euclidean__tactics.Col__nCol__False (B) (Q) (R) (H10)).
-----------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (Q) (R) (H8) (H4) H6).


--------- assert (* Cut *) (euclidean__axioms.Col Q R B) as H11.
---------- assert (* Cut *) ((euclidean__axioms.Col Q B R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))))) as H11.
----------- apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (R) H10).
----------- assert (* AndElim *) ((euclidean__axioms.Col Q B R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B)))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H14.
---------- assert (* Cut *) (euclidean__axioms.Col Q R P) as H12.
----------- assert (* Cut *) ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))))) as H12.
------------ apply (@lemma__collinearorder.lemma__collinearorder (P) (R) (Q) H9).
------------ assert (* AndElim *) ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P)))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H20.
----------- assert (* Cut *) (euclidean__axioms.neq Q R) as H13.
------------ assert (* Cut *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq Q P))) as H13.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (R) (P) H7).
------------- assert (* AndElim *) ((euclidean__axioms.neq R P) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq Q P))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq Q P)) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
exact H16.
------------ assert (* Cut *) (euclidean__axioms.Col R B P) as H14.
------------- apply (@euclidean__tactics.not__nCol__Col (R) (B) (P)).
--------------intro H14.
apply (@euclidean__tactics.Col__nCol__False (R) (B) (P) (H14)).
---------------apply (@lemma__collinear4.lemma__collinear4 (Q) (R) (B) (P) (H11) (H12) H13).


------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H15.
--------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (R) H4).
--------------- assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
exact H23.
-------------- assert (* Cut *) (euclidean__axioms.Col A P B) as H16.
--------------- assert (* Cut *) ((R = B) \/ (euclidean__axioms.neq R B)) as H16.
---------------- apply (@euclidean__tactics.eq__or__neq (R) B).
---------------- assert (* Cut *) ((R = B) \/ (euclidean__axioms.neq R B)) as H17.
----------------- exact H16.
----------------- assert (* Cut *) ((R = B) \/ (euclidean__axioms.neq R B)) as __TmpHyp.
------------------ exact H17.
------------------ assert (R = B \/ euclidean__axioms.neq R B) as H18.
------------------- exact __TmpHyp.
------------------- destruct H18 as [H18|H18].
-------------------- assert (* Cut *) (euclidean__axioms.Col P B Q) as H19.
--------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS P R0 Q) -> ((euclidean__axioms.Col A B R0) -> ((euclidean__axioms.BetS Q R0 P) -> ((euclidean__axioms.Col P R0 Q) -> ((euclidean__axioms.Col B Q R0) -> ((euclidean__axioms.Col Q R0 B) -> ((euclidean__axioms.Col Q R0 P) -> ((euclidean__axioms.neq Q R0) -> ((euclidean__axioms.Col R0 B P) -> ((euclidean__axioms.Col R0 B A) -> (euclidean__axioms.Col P B Q)))))))))))) with (x := R).
----------------------intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
exact H22.

---------------------- exact H18.
---------------------- exact H2.
---------------------- exact H4.
---------------------- exact H7.
---------------------- exact H9.
---------------------- exact H10.
---------------------- exact H11.
---------------------- exact H12.
---------------------- exact H13.
---------------------- exact H14.
---------------------- exact H15.
--------------------- assert (* Cut *) (euclidean__axioms.Col B Q P) as H20.
---------------------- assert (* Cut *) ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P))))) as H20.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (B) (Q) H19).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P))))) as H21.
------------------------ exact H20.
------------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P)))) as H23.
------------------------- exact H22.
------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P))) as H25.
-------------------------- exact H24.
-------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P)) as H27.
--------------------------- exact H26.
--------------------------- destruct H27 as [H27 H28].
exact H23.
---------------------- assert (* Cut *) (euclidean__axioms.Col B Q A) as H21.
----------------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H21.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (Q) H8).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H22.
------------------------- exact H21.
------------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)))) as H24.
-------------------------- exact H23.
-------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))) as H26.
--------------------------- exact H25.
--------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)) as H28.
---------------------------- exact H27.
---------------------------- destruct H28 as [H28 H29].
exact H24.
----------------------- assert (* Cut *) (euclidean__axioms.neq R Q) as H22.
------------------------ assert (* Cut *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H22.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (R) (Q) H2).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H23.
-------------------------- exact H22.
-------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q)) as H25.
--------------------------- exact H24.
--------------------------- destruct H25 as [H25 H26].
exact H23.
------------------------ assert (* Cut *) (euclidean__axioms.neq B Q) as H23.
------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS P R0 Q) -> ((euclidean__axioms.Col A B R0) -> ((euclidean__axioms.BetS Q R0 P) -> ((euclidean__axioms.Col P R0 Q) -> ((euclidean__axioms.Col B Q R0) -> ((euclidean__axioms.Col Q R0 B) -> ((euclidean__axioms.Col Q R0 P) -> ((euclidean__axioms.neq Q R0) -> ((euclidean__axioms.Col R0 B P) -> ((euclidean__axioms.Col R0 B A) -> ((euclidean__axioms.neq R0 Q) -> (euclidean__axioms.neq B Q))))))))))))) with (x := R).
--------------------------intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
exact H33.

-------------------------- exact H18.
-------------------------- exact H2.
-------------------------- exact H4.
-------------------------- exact H7.
-------------------------- exact H9.
-------------------------- exact H10.
-------------------------- exact H11.
-------------------------- exact H12.
-------------------------- exact H13.
-------------------------- exact H14.
-------------------------- exact H15.
-------------------------- exact H22.
------------------------- assert (* Cut *) (euclidean__axioms.Col Q P A) as H24.
-------------------------- apply (@euclidean__tactics.not__nCol__Col (Q) (P) (A)).
---------------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False (Q) (P) (A) (H24)).
----------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (Q) (P) (A) (H20) (H21) H23).


-------------------------- assert (* Cut *) (euclidean__axioms.Col Q P B) as H25.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B P Q) /\ (euclidean__axioms.Col P Q B))))) as H25.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (P) H20).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B P Q) /\ (euclidean__axioms.Col P Q B))))) as H26.
----------------------------- exact H25.
----------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B P Q) /\ (euclidean__axioms.Col P Q B)))) as H28.
------------------------------ exact H27.
------------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B P Q) /\ (euclidean__axioms.Col P Q B))) as H30.
------------------------------- exact H29.
------------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B P Q) /\ (euclidean__axioms.Col P Q B)) as H32.
-------------------------------- exact H31.
-------------------------------- destruct H32 as [H32 H33].
exact H28.
--------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H26.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H26.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (R) (Q) H2).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H27.
------------------------------ exact H26.
------------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q)) as H29.
------------------------------- exact H28.
------------------------------- destruct H29 as [H29 H30].
exact H30.
---------------------------- assert (* Cut *) (euclidean__axioms.neq Q P) as H27.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (Q) H26).
----------------------------- assert (* Cut *) (euclidean__axioms.Col P A B) as H28.
------------------------------ apply (@euclidean__tactics.not__nCol__Col (P) (A) (B)).
-------------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (P) (A) (B) (H28)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (P) (A) (B) (H24) (H25) H27).


------------------------------ assert (* Cut *) (euclidean__axioms.Col A P B) as H29.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))))) as H29.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (B) H28).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))))) as H30.
--------------------------------- exact H29.
--------------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P)))) as H32.
---------------------------------- exact H31.
---------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))) as H34.
----------------------------------- exact H33.
----------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P)) as H36.
------------------------------------ exact H35.
------------------------------------ destruct H36 as [H36 H37].
exact H30.
------------------------------- exact H29.
-------------------- assert (* Cut *) (euclidean__axioms.Col B P A) as H19.
--------------------- apply (@euclidean__tactics.not__nCol__Col (B) (P) (A)).
----------------------intro H19.
apply (@euclidean__tactics.Col__nCol__False (B) (P) (A) (H19)).
-----------------------apply (@lemma__collinear4.lemma__collinear4 (R) (B) (P) (A) (H14) (H15) H18).


--------------------- assert (* Cut *) (euclidean__axioms.Col A P B) as H20.
---------------------- assert (* Cut *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))))) as H20.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (P) (A) H19).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))))) as H21.
------------------------ exact H20.
------------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B)))) as H23.
------------------------- exact H22.
------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))) as H25.
-------------------------- exact H24.
-------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B)) as H27.
--------------------------- exact H26.
--------------------------- destruct H27 as [H27 H28].
exact H28.
---------------------- exact H20.
--------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H17.
---------------- assert (* Cut *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))))) as H17.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (P) (B) H16).
----------------- assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A)))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
exact H24.
---------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H5) H17).
------- assert (* Cut *) (euclidean__axioms.TS Q A B P) as H9.
-------- exists R.
split.
--------- exact H7.
--------- split.
---------- exact H4.
---------- apply (@euclidean__tactics.nCol__notCol (A) (B) (Q) H8).
-------- exact H9.
Qed.
