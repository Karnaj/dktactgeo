Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__angledistinct.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray4.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Definition lemma__equalanglestransitive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.CongA A B C D E F) -> ((euclidean__defs.CongA D E F P Q R) -> (euclidean__defs.CongA A B C P Q R)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro R.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A B) as H1.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H1.
-- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (F) H).
-- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
exact H2.
- assert (* Cut *) (euclidean__axioms.neq D E) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H2.
--- apply (@lemma__angledistinct.lemma__angledistinct (D) (E) (F) (P) (Q) (R) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H3.
-- assert (* Cut *) (euclidean__axioms.neq B A) as H3.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H1).
--- assert (* Cut *) (euclidean__axioms.neq E D) as H4.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H2).
---- assert (* Cut *) (euclidean__axioms.neq E F) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H5.
------ apply (@lemma__angledistinct.lemma__angledistinct (D) (E) (F) (P) (Q) (R) H0).
------ assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.neq B C) as H6.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H6.
------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (F) H).
------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
exact H9.
------ assert (* Cut *) (euclidean__axioms.neq P Q) as H7.
------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H7.
-------- apply (@lemma__angledistinct.lemma__angledistinct (D) (E) (F) (P) (Q) (R) H0).
-------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.neq Q P) as H8.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (Q) H7).
-------- assert (* Cut *) (exists (U: euclidean__axioms.Point), (euclidean__defs.Out E D U) /\ (euclidean__axioms.Cong E U B A)) as H9.
--------- apply (@lemma__layoff.lemma__layoff (E) (D) (B) (A) (H4) H3).
--------- assert (exists U: euclidean__axioms.Point, ((euclidean__defs.Out E D U) /\ (euclidean__axioms.Cong E U B A))) as H10.
---------- exact H9.
---------- destruct H10 as [U H10].
assert (* AndElim *) ((euclidean__defs.Out E D U) /\ (euclidean__axioms.Cong E U B A)) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* Cut *) (exists (V: euclidean__axioms.Point), (euclidean__defs.Out E F V) /\ (euclidean__axioms.Cong E V B C)) as H13.
------------ apply (@lemma__layoff.lemma__layoff (E) (F) (B) (C) (H5) H6).
------------ assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Out E F V) /\ (euclidean__axioms.Cong E V B C))) as H14.
------------- exact H13.
------------- destruct H14 as [V H14].
assert (* AndElim *) ((euclidean__defs.Out E F V) /\ (euclidean__axioms.Cong E V B C)) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* Cut *) (euclidean__axioms.neq E U) as H17.
--------------- apply (@lemma__raystrict.lemma__raystrict (E) (D) (U) H11).
--------------- assert (* Cut *) (euclidean__axioms.neq E V) as H18.
---------------- apply (@lemma__raystrict.lemma__raystrict (E) (F) (V) H15).
---------------- assert (* Cut *) (euclidean__defs.CongA P Q R D E F) as H19.
----------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (P) (Q) (R) H0).
----------------- assert (* Cut *) (euclidean__axioms.neq Q R) as H20.
------------------ assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H20.
------------------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H19).
------------------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
exact H23.
------------------ assert (* Cut *) (exists (u: euclidean__axioms.Point), (euclidean__defs.Out Q P u) /\ (euclidean__axioms.Cong Q u E U)) as H21.
------------------- apply (@lemma__layoff.lemma__layoff (Q) (P) (E) (U) (H8) H17).
------------------- assert (exists u: euclidean__axioms.Point, ((euclidean__defs.Out Q P u) /\ (euclidean__axioms.Cong Q u E U))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [u H22].
assert (* AndElim *) ((euclidean__defs.Out Q P u) /\ (euclidean__axioms.Cong Q u E U)) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* Cut *) (exists (v: euclidean__axioms.Point), (euclidean__defs.Out Q R v) /\ (euclidean__axioms.Cong Q v E V)) as H25.
---------------------- apply (@lemma__layoff.lemma__layoff (Q) (R) (E) (V) (H20) H18).
---------------------- assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out Q R v) /\ (euclidean__axioms.Cong Q v E V))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [v H26].
assert (* AndElim *) ((euclidean__defs.Out Q R v) /\ (euclidean__axioms.Cong Q v E V)) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.nCol A B C) as H29.
------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q U0 E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol P Q R)))))))) as H29.
-------------------------- exact H19.
-------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q U0 E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol P Q R)))))))) as __TmpHyp.
--------------------------- exact H29.
--------------------------- assert (exists U0: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q U0 E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol P Q R))))))))) as H30.
---------------------------- exact __TmpHyp.
---------------------------- destruct H30 as [x H30].
assert (exists V0: euclidean__axioms.Point, (exists (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q x E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong x V0 u0 v0) /\ (euclidean__axioms.nCol P Q R))))))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [x0 H31].
assert (exists u0: euclidean__axioms.Point, (exists (v0: euclidean__axioms.Point), (euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R x0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q x E u0) /\ ((euclidean__axioms.Cong Q x0 E v0) /\ ((euclidean__axioms.Cong x x0 u0 v0) /\ (euclidean__axioms.nCol P Q R))))))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [x1 H32].
assert (exists v0: euclidean__axioms.Point, ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R x0) /\ ((euclidean__defs.Out E D x1) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E v0) /\ ((euclidean__axioms.Cong x x0 x1 v0) /\ (euclidean__axioms.nCol P Q R))))))))) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [x2 H33].
assert (* AndElim *) ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R x0) /\ ((euclidean__defs.Out E D x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R)))))))) as H34.
-------------------------------- exact H33.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Out Q R x0) /\ ((euclidean__defs.Out E D x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R))))))) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Out E D x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R)))))) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong Q x E x1) /\ ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong Q x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol P Q R)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E U0 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol D E F)))))))) as H48.
--------------------------------------- exact H0.
--------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E U0 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol D E F)))))))) as __TmpHyp0.
---------------------------------------- exact H48.
---------------------------------------- assert (exists U0: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E U0 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol D E F))))))))) as H49.
----------------------------------------- exact __TmpHyp0.
----------------------------------------- destruct H49 as [x3 H49].
assert (exists V0: euclidean__axioms.Point, (exists (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out E D x3) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E x3 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong x3 V0 u0 v0) /\ (euclidean__axioms.nCol D E F))))))))) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [x4 H50].
assert (exists u0: euclidean__axioms.Point, (exists (v0: euclidean__axioms.Point), (euclidean__defs.Out E D x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E x3 Q u0) /\ ((euclidean__axioms.Cong E x4 Q v0) /\ ((euclidean__axioms.Cong x3 x4 u0 v0) /\ (euclidean__axioms.nCol D E F))))))))) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [x5 H51].
assert (exists v0: euclidean__axioms.Point, ((euclidean__defs.Out E D x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out Q P x5) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q v0) /\ ((euclidean__axioms.Cong x3 x4 x5 v0) /\ (euclidean__axioms.nCol D E F))))))))) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [x6 H52].
assert (* AndElim *) ((euclidean__defs.Out E D x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out Q P x5) /\ ((euclidean__defs.Out Q R x6) /\ ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F)))))))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out Q P x5) /\ ((euclidean__defs.Out Q R x6) /\ ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F))))))) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__defs.Out Q P x5) /\ ((euclidean__defs.Out Q R x6) /\ ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F)))))) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.Out Q R x6) /\ ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F))))) as H59.
------------------------------------------------ exact H58.
------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong E x3 Q x5) /\ ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F)))) as H61.
------------------------------------------------- exact H60.
------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Cong E x4 Q x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F))) as H63.
-------------------------------------------------- exact H62.
-------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol D E F)) as H65.
--------------------------------------------------- exact H64.
--------------------------------------------------- destruct H65 as [H65 H66].
assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out B A U0) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B U0 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol A B C)))))))) as H67.
---------------------------------------------------- exact H.
---------------------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out B A U0) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B U0 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp1.
----------------------------------------------------- exact H67.
----------------------------------------------------- assert (exists U0: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point) (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out B A U0) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B U0 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol A B C))))))))) as H68.
------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------ destruct H68 as [x7 H68].
assert (exists V0: euclidean__axioms.Point, (exists (u0: euclidean__axioms.Point) (v0: euclidean__axioms.Point), (euclidean__defs.Out B A x7) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B x7 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong x7 V0 u0 v0) /\ (euclidean__axioms.nCol A B C))))))))) as H69.
------------------------------------------------------- exact H68.
------------------------------------------------------- destruct H69 as [x8 H69].
assert (exists u0: euclidean__axioms.Point, (exists (v0: euclidean__axioms.Point), (euclidean__defs.Out B A x7) /\ ((euclidean__defs.Out B C x8) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B x7 E u0) /\ ((euclidean__axioms.Cong B x8 E v0) /\ ((euclidean__axioms.Cong x7 x8 u0 v0) /\ (euclidean__axioms.nCol A B C))))))))) as H70.
-------------------------------------------------------- exact H69.
-------------------------------------------------------- destruct H70 as [x9 H70].
assert (exists v0: euclidean__axioms.Point, ((euclidean__defs.Out B A x7) /\ ((euclidean__defs.Out B C x8) /\ ((euclidean__defs.Out E D x9) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E v0) /\ ((euclidean__axioms.Cong x7 x8 x9 v0) /\ (euclidean__axioms.nCol A B C))))))))) as H71.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- destruct H71 as [x10 H71].
assert (* AndElim *) ((euclidean__defs.Out B A x7) /\ ((euclidean__defs.Out B C x8) /\ ((euclidean__defs.Out E D x9) /\ ((euclidean__defs.Out E F x10) /\ ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C)))))))) as H72.
---------------------------------------------------------- exact H71.
---------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.Out B C x8) /\ ((euclidean__defs.Out E D x9) /\ ((euclidean__defs.Out E F x10) /\ ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C))))))) as H74.
----------------------------------------------------------- exact H73.
----------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__defs.Out E D x9) /\ ((euclidean__defs.Out E F x10) /\ ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C)))))) as H76.
------------------------------------------------------------ exact H75.
------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__defs.Out E F x10) /\ ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C))))) as H78.
------------------------------------------------------------- exact H77.
------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Cong B x7 E x9) /\ ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C)))) as H80.
-------------------------------------------------------------- exact H79.
-------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Cong B x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C))) as H82.
--------------------------------------------------------------- exact H81.
--------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol A B C)) as H84.
---------------------------------------------------------------- exact H83.
---------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
------------------------- assert (* Cut *) (euclidean__defs.CongA A B C U E V) as H30.
-------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (D) (E) (F) (U) (V) (H) (H11) H15).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong B A E U) as H31.
--------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (E) (U) (A) H12).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B C E V) as H32.
---------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (E) (V) (C) H16).
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H33.
----------------------------- apply (@proposition__04.proposition__04 (B) (A) (C) (E) (U) (V) (H31) (H32) H30).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong E U Q u) as H34.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (Q) (u) (U) H24).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong E V Q v) as H35.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H35.
-------------------------------- exact H33.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (Q) (v) (V) H28).
------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F u Q v) as H36.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H36.
--------------------------------- exact H33.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (P) (Q) (R) (u) (v) (H0) (H23) H27).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA u Q v D E F) as H37.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H37.
---------------------------------- exact H33.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (u) (Q) (v) H36).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA u Q v U E V) as H38.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H38.
----------------------------------- exact H33.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (u) (Q) (v) (D) (E) (F) (U) (V) (H37) (H11) H15).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA U E V u Q v) as H39.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H39.
------------------------------------ exact H33.
------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (u) (Q) (v) (U) (E) (V) H38).
----------------------------------- assert (* Cut *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H40.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H40.
------------------------------------- exact H33.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
apply (@proposition__04.proposition__04 (E) (U) (V) (Q) (u) (v) (H34) (H35) H39).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A C u v) as H41.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H45.
---------------------------------------- exact H33.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (C) (U) (V) (u) (v) (H45) H41).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A Q u) as H42.
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H42.
--------------------------------------- exact H40.
--------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H46.
----------------------------------------- exact H33.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (A) (E) (U) (Q) (u) (H31) H34).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C Q v) as H43.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H43.
---------------------------------------- exact H40.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H47.
------------------------------------------ exact H33.
------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (E) (V) (Q) (v) (H32) H35).
--------------------------------------- assert (* Cut *) (A = A) as H44.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H44.
----------------------------------------- exact H40.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H48.
------------------------------------------- exact H33.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
apply (@logic.eq__refl (Point) A).
---------------------------------------- assert (* Cut *) (C = C) as H45.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H45.
------------------------------------------ exact H40.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H49.
-------------------------------------------- exact H33.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
apply (@logic.eq__refl (Point) C).
----------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H46.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H46.
------------------------------------------- exact H40.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H50.
--------------------------------------------- exact H33.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H52.
---------------------------------------------- exact H51.
---------------------------------------------- destruct H52 as [H52 H53].
apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-----------------------------------------------right.
left.
exact H44.

----------------------------------------------- exact H3.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C C) as H47.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H47.
-------------------------------------------- exact H40.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u)) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H51.
---------------------------------------------- exact H33.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U)) as H53.
----------------------------------------------- exact H52.
----------------------------------------------- destruct H53 as [H53 H54].
apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
------------------------------------------------right.
left.
exact H45.

------------------------------------------------ exact H6.
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C P Q R) as H48.
-------------------------------------------- exists A.
exists C.
exists u.
exists v.
split.
--------------------------------------------- exact H46.
--------------------------------------------- split.
---------------------------------------------- exact H47.
---------------------------------------------- split.
----------------------------------------------- exact H23.
----------------------------------------------- split.
------------------------------------------------ exact H27.
------------------------------------------------ split.
------------------------------------------------- exact H42.
------------------------------------------------- split.
-------------------------------------------------- exact H43.
-------------------------------------------------- split.
--------------------------------------------------- exact H41.
--------------------------------------------------- exact H29.
-------------------------------------------- exact H48.
Qed.
