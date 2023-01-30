Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__twolines2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq C D) -> ((euclidean__axioms.Col P A B) -> ((euclidean__axioms.Col P C D) -> ((euclidean__axioms.Col Q A B) -> ((euclidean__axioms.Col Q C D) -> ((~((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col B C D))) -> (P = Q))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
assert (* Cut *) (euclidean__axioms.neq B A) as H6.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
- assert (* Cut *) (euclidean__axioms.neq D C) as H7.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H0).
-- assert (* Cut *) (~(euclidean__axioms.neq P Q)) as H8.
--- intro H8.
assert (* Cut *) (euclidean__axioms.Col D C P) as H9.
---- assert (* Cut *) ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P D C) /\ (euclidean__axioms.Col D C P))))) as H9.
----- apply (@lemma__collinearorder.lemma__collinearorder (P) (C) (D) H2).
----- assert (* AndElim *) ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P D C) /\ (euclidean__axioms.Col D C P))))) as H10.
------ exact H9.
------ destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P D C) /\ (euclidean__axioms.Col D C P)))) as H12.
------- exact H11.
------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P D C) /\ (euclidean__axioms.Col D C P))) as H14.
-------- exact H13.
-------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col P D C) /\ (euclidean__axioms.Col D C P)) as H16.
--------- exact H15.
--------- destruct H16 as [H16 H17].
exact H17.
---- assert (* Cut *) (euclidean__axioms.Col D C Q) as H10.
----- assert (* Cut *) ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))))) as H10.
------ apply (@lemma__collinearorder.lemma__collinearorder (Q) (C) (D) H4).
------ assert (* AndElim *) ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q)))) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))) as H15.
--------- exact H14.
--------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q)) as H17.
---------- exact H16.
---------- destruct H17 as [H17 H18].
exact H18.
----- assert (* Cut *) (euclidean__axioms.Col C P Q) as H11.
------ apply (@euclidean__tactics.not__nCol__Col (C) (P) (Q)).
-------intro H11.
apply (@euclidean__tactics.Col__nCol__False (C) (P) (Q) (H11)).
--------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (P) (Q) (H9) (H10) H7).


------ assert (* Cut *) (euclidean__axioms.Col A B P) as H12.
------- assert (* Cut *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))))) as H12.
-------- apply (@lemma__collinearorder.lemma__collinearorder (P) (A) (B) H1).
-------- assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P)))) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P))) as H17.
----------- exact H16.
----------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ (euclidean__axioms.Col B A P)) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
exact H15.
------- assert (* Cut *) (euclidean__axioms.Col A B Q) as H13.
-------- assert (* Cut *) ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q B A) /\ (euclidean__axioms.Col B A Q))))) as H13.
--------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (A) (B) H3).
--------- assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q B A) /\ (euclidean__axioms.Col B A Q))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q B A) /\ (euclidean__axioms.Col B A Q)))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q B A) /\ (euclidean__axioms.Col B A Q))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col Q B A) /\ (euclidean__axioms.Col B A Q)) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
exact H16.
-------- assert (* Cut *) (euclidean__axioms.Col B P Q) as H14.
--------- apply (@euclidean__tactics.not__nCol__Col (B) (P) (Q)).
----------intro H14.
apply (@euclidean__tactics.Col__nCol__False (B) (P) (Q) (H14)).
-----------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (P) (Q) (H12) (H13) H).


--------- assert (* Cut *) (euclidean__axioms.Col P Q B) as H15.
---------- assert (* Cut *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))))) as H15.
----------- apply (@lemma__collinearorder.lemma__collinearorder (B) (P) (Q) H14).
----------- assert (* AndElim *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B)))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B)) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
exact H18.
---------- assert (* Cut *) (euclidean__axioms.Col P Q C) as H16.
----------- assert (* Cut *) ((euclidean__axioms.Col P C Q) /\ ((euclidean__axioms.Col P Q C) /\ ((euclidean__axioms.Col Q C P) /\ ((euclidean__axioms.Col C Q P) /\ (euclidean__axioms.Col Q P C))))) as H16.
------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (P) (Q) H11).
------------ assert (* AndElim *) ((euclidean__axioms.Col P C Q) /\ ((euclidean__axioms.Col P Q C) /\ ((euclidean__axioms.Col Q C P) /\ ((euclidean__axioms.Col C Q P) /\ (euclidean__axioms.Col Q P C))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col P Q C) /\ ((euclidean__axioms.Col Q C P) /\ ((euclidean__axioms.Col C Q P) /\ (euclidean__axioms.Col Q P C)))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col Q C P) /\ ((euclidean__axioms.Col C Q P) /\ (euclidean__axioms.Col Q P C))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col C Q P) /\ (euclidean__axioms.Col Q P C)) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
exact H19.
----------- assert (* Cut *) (euclidean__axioms.Col Q C B) as H17.
------------ apply (@euclidean__tactics.not__nCol__Col (Q) (C) (B)).
-------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (Q) (C) (B) (H17)).
--------------apply (@lemma__collinear4.lemma__collinear4 (P) (Q) (C) (B) (H16) (H15) H8).


------------ assert (* Cut *) (euclidean__axioms.Col Q C D) as H18.
------------- assert (* Cut *) ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))))) as H18.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (C) (B) H17).
-------------- assert (* AndElim *) ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q)))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col Q B C) /\ (euclidean__axioms.Col B C Q)) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
exact H4.
------------- assert (* Cut *) (~(Q = C)) as H19.
-------------- intro H19.
assert (* Cut *) (euclidean__axioms.Col C P D) as H20.
--------------- assert (* Cut *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H20.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (P) H9).
---------------- assert (* AndElim *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
exact H23.
--------------- assert (* Cut *) (euclidean__axioms.Col Q P B) as H21.
---------------- assert (* Cut *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))))) as H21.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (B) H15).
----------------- assert (* AndElim *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P)))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P)) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
exact H22.
---------------- assert (* Cut *) (euclidean__axioms.Col B A Q) as H22.
----------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H22.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (Q) H13).
------------------ assert (* AndElim *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
exact H23.
----------------- assert (* Cut *) (euclidean__axioms.Col B A P) as H23.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H23.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (P) H12).
------------------- assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
exact H24.
------------------ assert (* Cut *) (euclidean__axioms.Col A Q P) as H24.
------------------- apply (@euclidean__tactics.not__nCol__Col (A) (Q) (P)).
--------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False (A) (Q) (P) (H24)).
---------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (Q) (P) (H22) (H23) H6).


------------------- assert (* Cut *) (euclidean__axioms.Col Q P A) as H25.
-------------------- assert (* Cut *) ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col A P Q) /\ (euclidean__axioms.Col P Q A))))) as H25.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (Q) (P) H24).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col A P Q) /\ (euclidean__axioms.Col P Q A))))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col A P Q) /\ (euclidean__axioms.Col P Q A)))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col A P Q) /\ (euclidean__axioms.Col P Q A))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ (euclidean__axioms.Col P Q A)) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
exact H28.
-------------------- assert (* Cut *) (euclidean__axioms.Col C P B) as H26.
--------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun Q0: euclidean__axioms.Point => (euclidean__axioms.Col Q0 A B) -> ((euclidean__axioms.Col Q0 C D) -> ((euclidean__axioms.neq P Q0) -> ((euclidean__axioms.Col D C Q0) -> ((euclidean__axioms.Col C P Q0) -> ((euclidean__axioms.Col A B Q0) -> ((euclidean__axioms.Col B P Q0) -> ((euclidean__axioms.Col P Q0 B) -> ((euclidean__axioms.Col P Q0 C) -> ((euclidean__axioms.Col Q0 C B) -> ((euclidean__axioms.Col Q0 C D) -> ((euclidean__axioms.Col Q0 P B) -> ((euclidean__axioms.Col B A Q0) -> ((euclidean__axioms.Col A Q0 P) -> ((euclidean__axioms.Col Q0 P A) -> (euclidean__axioms.Col C P B))))))))))))))))) with (x := Q).
----------------------intro H26.
intro H27.
intro H28.
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
exact H37.

---------------------- exact H19.
---------------------- exact H3.
---------------------- exact H4.
---------------------- exact H8.
---------------------- exact H10.
---------------------- exact H11.
---------------------- exact H13.
---------------------- exact H14.
---------------------- exact H15.
---------------------- exact H16.
---------------------- exact H17.
---------------------- exact H18.
---------------------- exact H21.
---------------------- exact H22.
---------------------- exact H24.
---------------------- exact H25.
--------------------- assert (* Cut *) (euclidean__axioms.Col C P A) as H27.
---------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun Q0: euclidean__axioms.Point => (euclidean__axioms.Col Q0 A B) -> ((euclidean__axioms.Col Q0 C D) -> ((euclidean__axioms.neq P Q0) -> ((euclidean__axioms.Col D C Q0) -> ((euclidean__axioms.Col C P Q0) -> ((euclidean__axioms.Col A B Q0) -> ((euclidean__axioms.Col B P Q0) -> ((euclidean__axioms.Col P Q0 B) -> ((euclidean__axioms.Col P Q0 C) -> ((euclidean__axioms.Col Q0 C B) -> ((euclidean__axioms.Col Q0 C D) -> ((euclidean__axioms.Col Q0 P B) -> ((euclidean__axioms.Col B A Q0) -> ((euclidean__axioms.Col A Q0 P) -> ((euclidean__axioms.Col Q0 P A) -> (euclidean__axioms.Col C P A))))))))))))))))) with (x := Q).
-----------------------intro H27.
intro H28.
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
exact H41.

----------------------- exact H19.
----------------------- exact H3.
----------------------- exact H4.
----------------------- exact H8.
----------------------- exact H10.
----------------------- exact H11.
----------------------- exact H13.
----------------------- exact H14.
----------------------- exact H15.
----------------------- exact H16.
----------------------- exact H17.
----------------------- exact H18.
----------------------- exact H21.
----------------------- exact H22.
----------------------- exact H24.
----------------------- exact H25.
---------------------- assert (* Cut *) (euclidean__axioms.Col P C A) as H28.
----------------------- assert (* Cut *) ((euclidean__axioms.Col P C A) /\ ((euclidean__axioms.Col P A C) /\ ((euclidean__axioms.Col A C P) /\ ((euclidean__axioms.Col C A P) /\ (euclidean__axioms.Col A P C))))) as H28.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (P) (A) H27).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col P C A) /\ ((euclidean__axioms.Col P A C) /\ ((euclidean__axioms.Col A C P) /\ ((euclidean__axioms.Col C A P) /\ (euclidean__axioms.Col A P C))))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col P A C) /\ ((euclidean__axioms.Col A C P) /\ ((euclidean__axioms.Col C A P) /\ (euclidean__axioms.Col A P C)))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A C P) /\ ((euclidean__axioms.Col C A P) /\ (euclidean__axioms.Col A P C))) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C A P) /\ (euclidean__axioms.Col A P C)) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
exact H29.
----------------------- assert (* Cut *) (euclidean__axioms.Col P C B) as H29.
------------------------ assert (* Cut *) ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col C B P) /\ (euclidean__axioms.Col B P C))))) as H29.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (P) (B) H26).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col C B P) /\ (euclidean__axioms.Col B P C))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col C B P) /\ (euclidean__axioms.Col B P C)))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B C P) /\ ((euclidean__axioms.Col C B P) /\ (euclidean__axioms.Col B P C))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col C B P) /\ (euclidean__axioms.Col B P C)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H30.
------------------------ assert (* Cut *) (euclidean__axioms.Col P C D) as H30.
------------------------- assert (* Cut *) ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P B C) /\ (euclidean__axioms.Col B C P))))) as H30.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (C) (B) H29).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P B C) /\ (euclidean__axioms.Col B C P))))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P B C) /\ (euclidean__axioms.Col B C P)))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B P C) /\ ((euclidean__axioms.Col P B C) /\ (euclidean__axioms.Col B C P))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col P B C) /\ (euclidean__axioms.Col B C P)) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
exact H2.
------------------------- assert (* Cut *) (~(P = C)) as H31.
-------------------------- intro H31.
assert (* Cut *) (P = Q) as H32.
--------------------------- apply (@logic.eq__trans (Point) (P) (C) (Q) (H31)).
----------------------------apply (@logic.eq__sym (Point) (Q) (C) H19).

--------------------------- apply (@H8 H32).
-------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H32.
--------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
----------------------------intro H32.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H32)).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (C) (D) (A) (H30) (H28) H31).


--------------------------- assert (* Cut *) (euclidean__axioms.Col C D B) as H33.
---------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (B)).
-----------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (B) (H33)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (C) (D) (B) (H30) (H29) H31).


---------------------------- assert (* Cut *) (euclidean__axioms.Col A C D) as H34.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H34.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (A) H32).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H39.
----------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H35.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H35.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (B) H33).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
exact H40.
------------------------------ apply (@H5).
-------------------------------split.
-------------------------------- exact H34.
-------------------------------- exact H35.

-------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H20.
--------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (D)).
----------------intro H20.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (D) (H20)).
-----------------apply (@lemma__collinear4.lemma__collinear4 (Q) (C) (B) (D) (H17) (H18) H19).


--------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
---------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H21.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H20).
----------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
exact H22.
---------------- assert (* Cut *) (~(B = A)) as H22.
----------------- intro H22.
assert (* Cut *) (A = B) as H23.
------------------ apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (B) H22).
------------------ apply (@H H23).
----------------- assert (* Cut *) (euclidean__axioms.Col B A P) as H23.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H23.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (P) H12).
------------------- assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
exact H24.
------------------ assert (* Cut *) (euclidean__axioms.Col B A Q) as H24.
------------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H24.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (Q) H13).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)))) as H27.
---------------------- exact H26.
---------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A)) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
exact H25.
------------------- assert (* Cut *) (euclidean__axioms.Col A P Q) as H25.
-------------------- apply (@euclidean__tactics.not__nCol__Col (A) (P) (Q)).
---------------------intro H25.
apply (@euclidean__tactics.Col__nCol__False (A) (P) (Q) (H25)).
----------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (P) (Q) (H23) (H24) H22).


-------------------- assert (* Cut *) (euclidean__axioms.Col P Q A) as H26.
--------------------- assert (* Cut *) ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A))))) as H26.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (P) (Q) H25).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H29.
--------------------- assert (* Cut *) (euclidean__axioms.Col P Q C) as H27.
---------------------- assert (* Cut *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))))) as H27.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (A) H26).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P)))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P)) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
exact H16.
---------------------- assert (* Cut *) (euclidean__axioms.Col Q C A) as H28.
----------------------- apply (@euclidean__tactics.not__nCol__Col (Q) (C) (A)).
------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (Q) (C) (A) (H28)).
-------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (Q) (C) (A) (H27) (H26) H8).


----------------------- assert (* Cut *) (euclidean__axioms.Col Q C D) as H29.
------------------------ assert (* Cut *) ((euclidean__axioms.Col C Q A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A Q C) /\ ((euclidean__axioms.Col Q A C) /\ (euclidean__axioms.Col A C Q))))) as H29.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (C) (A) H28).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col C Q A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A Q C) /\ ((euclidean__axioms.Col Q A C) /\ (euclidean__axioms.Col A C Q))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A Q C) /\ ((euclidean__axioms.Col Q A C) /\ (euclidean__axioms.Col A C Q)))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A Q C) /\ ((euclidean__axioms.Col Q A C) /\ (euclidean__axioms.Col A C Q))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col Q A C) /\ (euclidean__axioms.Col A C Q)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H18.
------------------------ assert (* Cut *) (euclidean__axioms.Col C A D) as H30.
------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (A) (D)).
--------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (D) (H30)).
---------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (C) (A) (D) (H28) (H29) H19).


------------------------- assert (* Cut *) (euclidean__axioms.Col A C D) as H31.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))))) as H31.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (D) H30).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C)))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C)) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
exact H32.
-------------------------- apply (@H5).
---------------------------split.
---------------------------- exact H31.
---------------------------- exact H21.

--- apply (@euclidean__tactics.NNPP (P = Q)).
----intro H9.
assert (* Cut *) (False) as H10.
----- apply (@H8 H9).
----- assert (* Cut *) ((euclidean__axioms.Col A C D) -> ((euclidean__axioms.Col B C D) -> False)) as H11.
------ intro H11.
intro H12.
apply (@H5).
-------split.
-------- exact H11.
-------- exact H12.

------ assert False.
-------exact H10.
------- contradiction.

Qed.
