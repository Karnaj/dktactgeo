Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__supplements.
Require Export logic.
Definition proposition__15 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C E D) -> ((euclidean__axioms.nCol A E C) -> ((euclidean__defs.CongA A E C D E B) /\ (euclidean__defs.CongA C E B A E D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq E D) as H2.
- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H2.
-- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (D) H0).
-- assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
exact H3.
- assert (* Cut *) (euclidean__axioms.neq D E) as H3.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (D) H2).
-- assert (* Cut *) (euclidean__axioms.neq E B) as H4.
--- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H4.
---- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H).
---- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
exact H5.
--- assert (* Cut *) (euclidean__axioms.neq B E) as H5.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (B) H4).
---- assert (* Cut *) (~(euclidean__axioms.Col B E D)) as H6.
----- intro H6.
assert (* Cut *) (euclidean__axioms.Col A E B) as H7.
------ right.
right.
right.
right.
left.
exact H.
------ assert (* Cut *) (euclidean__axioms.Col B E A) as H8.
------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H8.
-------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H7).
-------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
exact H16.
------- assert (* Cut *) (euclidean__axioms.Col E A D) as H9.
-------- apply (@euclidean__tactics.not__nCol__Col (E) (A) (D)).
---------intro H9.
apply (@euclidean__tactics.Col__nCol__False (E) (A) (D) (H9)).
----------apply (@lemma__collinear4.lemma__collinear4 (B) (E) (A) (D) (H8) (H6) H5).


-------- assert (* Cut *) (euclidean__axioms.Col C E D) as H10.
--------- right.
right.
right.
right.
left.
exact H0.
--------- assert (* Cut *) (euclidean__axioms.Col D E C) as H11.
---------- assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H11.
----------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (D) H10).
----------- assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H19.
---------- assert (* Cut *) (euclidean__axioms.Col D E A) as H12.
----------- assert (* Cut *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H12.
------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (D) H9).
------------ assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H17.
----------- assert (* Cut *) (euclidean__axioms.Col E C A) as H13.
------------ apply (@euclidean__tactics.not__nCol__Col (E) (C) (A)).
-------------intro H13.
apply (@euclidean__tactics.Col__nCol__False (E) (C) (A) (H13)).
--------------apply (@lemma__collinear4.lemma__collinear4 (D) (E) (C) (A) (H11) (H12) H3).


------------ assert (* Cut *) (euclidean__axioms.Col A E C) as H14.
------------- assert (* Cut *) ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))))) as H14.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (A) H13).
-------------- assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E)))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E)) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
exact H19.
------------- apply (@euclidean__tactics.Col__nCol__False (A) (E) (C) (H1) H14).
----- assert (* Cut *) (D = D) as H7.
------ apply (@logic.eq__refl (Point) D).
------ assert (* Cut *) (B = B) as H8.
------- apply (@logic.eq__refl (Point) B).
------- assert (* Cut *) (C = C) as H9.
-------- apply (@logic.eq__refl (Point) C).
-------- assert (* Cut *) (euclidean__defs.Out E D D) as H10.
--------- apply (@lemma__ray4.lemma__ray4 (E) (D) (D)).
----------right.
left.
exact H7.

---------- exact H2.
--------- assert (* Cut *) (euclidean__defs.Out E B B) as H11.
---------- apply (@lemma__ray4.lemma__ray4 (E) (B) (B)).
-----------right.
left.
exact H8.

----------- exact H4.
---------- assert (* Cut *) (euclidean__axioms.BetS B E A) as H12.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (B) H).
----------- assert (* Cut *) (euclidean__defs.Supp B E D D A) as H13.
------------ split.
------------- exact H10.
------------- exact H12.
------------ assert (* Cut *) (euclidean__axioms.BetS D E C) as H14.
------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (E) (D) H0).
------------- assert (* Cut *) (euclidean__defs.Supp D E B B C) as H15.
-------------- split.
--------------- exact H11.
--------------- exact H14.
-------------- assert (* Cut *) (~(euclidean__axioms.Col A E D)) as H16.
--------------- intro H16.
assert (* Cut *) (euclidean__axioms.Col C E D) as H17.
---------------- right.
right.
right.
right.
left.
exact H0.
---------------- assert (* Cut *) (euclidean__axioms.Col D E C) as H18.
----------------- assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H18.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (D) H17).
------------------ assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
exact H26.
----------------- assert (* Cut *) (euclidean__axioms.Col D E A) as H19.
------------------ assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H19.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (D) H16).
------------------- assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H20.
-------------------- exact H19.
-------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)))) as H22.
--------------------- exact H21.
--------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
exact H27.
------------------ assert (* Cut *) (euclidean__axioms.Col E C A) as H20.
------------------- apply (@euclidean__tactics.not__nCol__Col (E) (C) (A)).
--------------------intro H20.
apply (@euclidean__tactics.Col__nCol__False (E) (C) (A) (H20)).
---------------------apply (@lemma__collinear4.lemma__collinear4 (D) (E) (C) (A) (H18) (H19) H3).


------------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H21.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))))) as H21.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (A) H20).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))))) as H22.
---------------------- exact H21.
---------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E)))) as H24.
----------------------- exact H23.
----------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ (euclidean__axioms.Col A C E)) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
exact H26.
-------------------- apply (@H6).
---------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (D)).
----------------------intro H22.
apply (@euclidean__tactics.Col__nCol__False (A) (E) (C) (H1) H21).


--------------- assert (* Cut *) (euclidean__defs.CongA B E D D E B) as H17.
---------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (E) (D)).
-----------------apply (@euclidean__tactics.nCol__notCol (B) (E) (D) H6).

---------------- assert (* Cut *) (euclidean__defs.CongA D E A B E C) as H18.
----------------- apply (@lemma__supplements.lemma__supplements (B) (E) (D) (D) (A) (D) (E) (B) (B) (C) (H17) (H13) H15).
----------------- assert (* Cut *) (~(euclidean__axioms.Col B E C)) as H19.
------------------ intro H19.
assert (* Cut *) (euclidean__axioms.Col A E B) as H20.
------------------- right.
right.
right.
right.
left.
exact H.
------------------- assert (* Cut *) (euclidean__axioms.Col B E A) as H21.
-------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H21.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H20).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H22.
---------------------- exact H21.
---------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H24.
----------------------- exact H23.
----------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
exact H29.
-------------------- assert (* Cut *) (euclidean__axioms.Col E A C) as H22.
--------------------- apply (@euclidean__tactics.not__nCol__Col (E) (A) (C)).
----------------------intro H22.
apply (@euclidean__tactics.Col__nCol__False (E) (A) (C) (H22)).
-----------------------apply (@lemma__collinear4.lemma__collinear4 (B) (E) (A) (C) (H21) (H19) H5).


--------------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H23.
---------------------- assert (* Cut *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E C A) /\ (euclidean__axioms.Col C A E))))) as H23.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (C) H22).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E C A) /\ (euclidean__axioms.Col C A E))))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E C A) /\ (euclidean__axioms.Col C A E)))) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E C A) /\ (euclidean__axioms.Col C A E))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ (euclidean__axioms.Col C A E)) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
exact H24.
---------------------- apply (@H6).
-----------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (D)).
------------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False (A) (E) (C) (H1) H23).


------------------ assert (* Cut *) (euclidean__defs.CongA B E C C E B) as H20.
------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (E) (C)).
--------------------apply (@euclidean__tactics.nCol__notCol (B) (E) (C) H19).

------------------- assert (* Cut *) (euclidean__defs.CongA D E A C E B) as H21.
-------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (D) (E) (A) (B) (E) (C) (C) (E) (B) (H18) H20).
-------------------- assert (* Cut *) (euclidean__defs.CongA A E D D E A) as H22.
--------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (E) (D)).
----------------------apply (@euclidean__tactics.nCol__notCol (A) (E) (D) H16).

--------------------- assert (* Cut *) (euclidean__defs.CongA A E D C E B) as H23.
---------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (E) (D) (D) (E) (A) (C) (E) (B) (H22) H21).
---------------------- assert (* Cut *) (euclidean__defs.CongA C E B A E D) as H24.
----------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (E) (D) (C) (E) (B) H23).
----------------------- assert (* Cut *) (~(E = C)) as H25.
------------------------ intro H25.
assert (* Cut *) (euclidean__axioms.Col B E C) as H26.
------------------------- right.
right.
left.
exact H25.
------------------------- apply (@H6).
--------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (D)).
---------------------------intro H27.
apply (@H19 H26).


------------------------ assert (* Cut *) (euclidean__defs.Out E C C) as H26.
------------------------- apply (@lemma__ray4.lemma__ray4 (E) (C) (C)).
--------------------------right.
left.
exact H9.

-------------------------- exact H25.
------------------------- assert (* Cut *) (euclidean__defs.Supp B E C C A) as H27.
-------------------------- split.
--------------------------- exact H26.
--------------------------- exact H12.
-------------------------- assert (* Cut *) (euclidean__axioms.BetS C E D) as H28.
--------------------------- exact H0.
--------------------------- assert (* Cut *) (euclidean__defs.Supp C E B B D) as H29.
---------------------------- split.
----------------------------- exact H11.
----------------------------- exact H28.
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col A E C)) as H30.
----------------------------- intro H30.
assert (* Cut *) (euclidean__axioms.Col D E C) as H31.
------------------------------ right.
right.
right.
right.
left.
exact H14.
------------------------------ assert (* Cut *) (euclidean__axioms.Col C E D) as H32.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col D C E) /\ (euclidean__axioms.Col C E D))))) as H32.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (C) H31).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col D C E) /\ (euclidean__axioms.Col C E D))))) as H33.
--------------------------------- exact H32.
--------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col D C E) /\ (euclidean__axioms.Col C E D)))) as H35.
---------------------------------- exact H34.
---------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col D C E) /\ (euclidean__axioms.Col C E D))) as H37.
----------------------------------- exact H36.
----------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ (euclidean__axioms.Col C E D)) as H39.
------------------------------------ exact H38.
------------------------------------ destruct H39 as [H39 H40].
exact H40.
------------------------------- assert (* Cut *) (euclidean__axioms.Col C E A) as H33.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H33.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H30).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H34.
---------------------------------- exact H33.
---------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H36.
----------------------------------- exact H35.
----------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
exact H41.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H34.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H34.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (D) H28).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H35.
----------------------------------- exact H34.
----------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D)) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [H37 H38].
exact H37.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H35.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (D) (A)).
-----------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (E) (D) (A) (H35)).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (E) (D) (A) (H32) (H33) H34).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H36.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E A D) /\ (euclidean__axioms.Col A D E))))) as H36.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (A) H35).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E A D) /\ (euclidean__axioms.Col A D E))))) as H37.
------------------------------------- exact H36.
------------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E A D) /\ (euclidean__axioms.Col A D E)))) as H39.
-------------------------------------- exact H38.
-------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E A D) /\ (euclidean__axioms.Col A D E))) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ (euclidean__axioms.Col A D E)) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
exact H41.
----------------------------------- apply (@H6).
------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (D)).
-------------------------------------intro H37.
apply (@H16 H36).


----------------------------- assert (* Cut *) (euclidean__defs.CongA B E C C E B) as H31.
------------------------------ exact H20.
------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A B E D) as H32.
------------------------------- apply (@lemma__supplements.lemma__supplements (B) (E) (C) (C) (A) (C) (E) (B) (B) (D) (H31) (H27) H29).
------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B E D)) as H33.
-------------------------------- intro H33.
assert (* Cut *) (euclidean__axioms.Col A E B) as H34.
--------------------------------- right.
right.
right.
right.
left.
exact H.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B E A) as H35.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H35.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H34).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H36.
------------------------------------ exact H35.
------------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H38.
------------------------------------- exact H37.
------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H40.
-------------------------------------- exact H39.
-------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [H42 H43].
exact H43.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H36.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (A) (D)).
------------------------------------intro H36.
apply (@H6 H33).

----------------------------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H37.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H37.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (D) H36).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H38.
-------------------------------------- exact H37.
-------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)))) as H40.
--------------------------------------- exact H39.
--------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
exact H38.
------------------------------------ apply (@H6 H33).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA B E D D E B) as H34.
--------------------------------- exact H17.
--------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A D E B) as H35.
---------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (C) (E) (A) (B) (E) (D) (D) (E) (B) (H32) H34).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA A E C C E A) as H36.
----------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (E) (C) H1).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA A E C D E B) as H37.
------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (E) (C) (C) (E) (A) (D) (E) (B) (H36) H35).
------------------------------------ split.
------------------------------------- exact H37.
------------------------------------- exact H24.
Qed.
Definition proposition__15a : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C E D) -> ((euclidean__axioms.nCol A E C) -> (euclidean__defs.CongA A E C D E B))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C E D) -> ((euclidean__axioms.nCol A E C) -> (euclidean__defs.CongA A E C D E B)))) as H2.
- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA A E C D E B) /\ (euclidean__defs.CongA C E B A E D)) as __2.
-- apply (@proposition__15.proposition__15 (A) (B) (C) (D) (E) (__) (__0) __1).
-- destruct __2 as [__2 __3].
exact __2.
- apply (@H2 (H) (H0) H1).
Qed.
Definition proposition__15b : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C E D) -> ((euclidean__axioms.nCol A E C) -> (euclidean__defs.CongA C E B A E D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C E D) -> ((euclidean__axioms.nCol A E C) -> (euclidean__defs.CongA C E B A E D)))) as H2.
- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA A E C D E B) /\ (euclidean__defs.CongA C E B A E D)) as __2.
-- apply (@proposition__15.proposition__15 (A) (B) (C) (D) (E) (__) (__0) __1).
-- destruct __2 as [__2 __3].
exact __3.
- apply (@H2 (H) (H0) H1).
Qed.
