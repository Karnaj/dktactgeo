Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__congruencesymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Require Export proposition__31short.
Require Export proposition__38.
Require Export proposition__39.
Definition proposition__40 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__axioms.Cong B C H E) -> ((euclidean__axioms.ET A B C D H E) -> ((euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D H E) -> ((euclidean__axioms.Col B C H) -> ((euclidean__axioms.Col B C E) -> ((euclidean__defs.OS A D B C) -> ((euclidean__axioms.neq A D) -> (euclidean__defs.Par A D B C)))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
assert (* Cut *) (euclidean__axioms.nCol D H E) as H8.
- exact H3.
- assert (* Cut *) (euclidean__axioms.neq H E) as H9.
-- assert (* Cut *) ((euclidean__axioms.neq D H) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D)))))) as H9.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (H) (E) H8).
--- assert (* AndElim *) ((euclidean__axioms.neq D H) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D)))))) as H10.
---- exact H9.
---- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D))))) as H12.
----- exact H11.
----- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D)))) as H14.
------ exact H13.
------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D))) as H16.
------- exact H15.
------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E D)) as H18.
-------- exact H17.
-------- destruct H18 as [H18 H19].
exact H12.
-- assert (* Cut *) (euclidean__axioms.neq E H) as H10.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H) (E) H9).
--- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS E H R) /\ (euclidean__axioms.Cong H R E H)) as H11.
---- apply (@lemma__extension.lemma__extension (E) (H) (E) (H) (H10) H10).
---- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS E H R) /\ (euclidean__axioms.Cong H R E H))) as H12.
----- exact H11.
----- destruct H12 as [R H12].
assert (* AndElim *) ((euclidean__axioms.BetS E H R) /\ (euclidean__axioms.Cong H R E H)) as H13.
------ exact H12.
------ destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.BetS R H E) as H15.
------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (H) (R) H13).
------- assert (* Cut *) (euclidean__axioms.nCol H E D) as H16.
-------- assert (* Cut *) ((euclidean__axioms.nCol H D E) /\ ((euclidean__axioms.nCol H E D) /\ ((euclidean__axioms.nCol E D H) /\ ((euclidean__axioms.nCol D E H) /\ (euclidean__axioms.nCol E H D))))) as H16.
--------- apply (@lemma__NCorder.lemma__NCorder (D) (H) (E) H8).
--------- assert (* AndElim *) ((euclidean__axioms.nCol H D E) /\ ((euclidean__axioms.nCol H E D) /\ ((euclidean__axioms.nCol E D H) /\ ((euclidean__axioms.nCol D E H) /\ (euclidean__axioms.nCol E H D))))) as H17.
---------- exact H16.
---------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol H E D) /\ ((euclidean__axioms.nCol E D H) /\ ((euclidean__axioms.nCol D E H) /\ (euclidean__axioms.nCol E H D)))) as H19.
----------- exact H18.
----------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol E D H) /\ ((euclidean__axioms.nCol D E H) /\ (euclidean__axioms.nCol E H D))) as H21.
------------ exact H20.
------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol D E H) /\ (euclidean__axioms.nCol E H D)) as H23.
------------- exact H22.
------------- destruct H23 as [H23 H24].
exact H19.
-------- assert (* Cut *) (euclidean__axioms.Col R H E) as H17.
--------- right.
right.
right.
right.
left.
exact H15.
--------- assert (* Cut *) (euclidean__axioms.Col H E R) as H18.
---------- assert (* Cut *) ((euclidean__axioms.Col H R E) /\ ((euclidean__axioms.Col H E R) /\ ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R E H) /\ (euclidean__axioms.Col E H R))))) as H18.
----------- apply (@lemma__collinearorder.lemma__collinearorder (R) (H) (E) H17).
----------- assert (* AndElim *) ((euclidean__axioms.Col H R E) /\ ((euclidean__axioms.Col H E R) /\ ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R E H) /\ (euclidean__axioms.Col E H R))))) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col H E R) /\ ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R E H) /\ (euclidean__axioms.Col E H R)))) as H21.
------------- exact H20.
------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R E H) /\ (euclidean__axioms.Col E H R))) as H23.
-------------- exact H22.
-------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col R E H) /\ (euclidean__axioms.Col E H R)) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
exact H21.
---------- assert (* Cut *) (E = E) as H19.
----------- apply (@logic.eq__refl (Point) E).
----------- assert (* Cut *) (euclidean__axioms.Col H E E) as H20.
------------ right.
right.
left.
exact H19.
------------ assert (* Cut *) (euclidean__axioms.neq R E) as H21.
------------- assert (* Cut *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq R H) /\ (euclidean__axioms.neq R E))) as H21.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal (R) (H) (E) H15).
-------------- assert (* AndElim *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq R H) /\ (euclidean__axioms.neq R E))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq R H) /\ (euclidean__axioms.neq R E)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
exact H25.
------------- assert (* Cut *) (euclidean__axioms.nCol R E D) as H22.
-------------- apply (@euclidean__tactics.nCol__notCol (R) (E) (D)).
---------------apply (@euclidean__tactics.nCol__not__Col (R) (E) (D)).
----------------apply (@lemma__NChelper.lemma__NChelper (H) (E) (D) (R) (E) (H16) (H18) (H20) H21).


-------------- assert (* Cut *) (exists (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS P D Q) /\ ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H))))) as H23.
--------------- apply (@proposition__31short.proposition__31short (D) (R) (E) (H) (H15) H22).
--------------- assert (exists P: euclidean__axioms.Point, (exists (Q: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS P D Q) /\ ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H)))))) as H24.
---------------- exact H23.
---------------- destruct H24 as [P H24].
assert (exists Q: euclidean__axioms.Point, (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS P D Q) /\ ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H)))))) as H25.
----------------- exact H24.
----------------- destruct H25 as [Q H25].
assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS P D Q) /\ ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H)))))) as H26.
------------------ exact H25.
------------------ destruct H26 as [M H26].
assert (* AndElim *) ((euclidean__axioms.BetS P D Q) /\ ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H))))) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.CongA P D H D H E) /\ ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H)))) as H29.
-------------------- exact H28.
-------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Par P Q R E) /\ ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.BetS P M E) /\ (euclidean__axioms.BetS D M H)) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__axioms.Col R E H) as H35.
----------------------- assert (* Cut *) ((euclidean__axioms.Col E H R) /\ ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R H E) /\ ((euclidean__axioms.Col H R E) /\ (euclidean__axioms.Col R E H))))) as H35.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (H) (E) (R) H18).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col E H R) /\ ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R H E) /\ ((euclidean__axioms.Col H R E) /\ (euclidean__axioms.Col R E H))))) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E R H) /\ ((euclidean__axioms.Col R H E) /\ ((euclidean__axioms.Col H R E) /\ (euclidean__axioms.Col R E H)))) as H38.
-------------------------- exact H37.
-------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col R H E) /\ ((euclidean__axioms.Col H R E) /\ (euclidean__axioms.Col R E H))) as H40.
--------------------------- exact H39.
--------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col H R E) /\ (euclidean__axioms.Col R E H)) as H42.
---------------------------- exact H41.
---------------------------- destruct H42 as [H42 H43].
exact H43.
----------------------- assert (* Cut *) (euclidean__defs.Par P Q H E) as H36.
------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (P) (Q) (H) (R) (E) (H31) (H35) H9).
------------------------ assert (* Cut *) (euclidean__axioms.Col P D Q) as H37.
------------------------- right.
right.
right.
right.
left.
exact H27.
------------------------- assert (* Cut *) (euclidean__axioms.Col P Q D) as H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col D P Q) /\ ((euclidean__axioms.Col D Q P) /\ ((euclidean__axioms.Col Q P D) /\ ((euclidean__axioms.Col P Q D) /\ (euclidean__axioms.Col Q D P))))) as H38.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (D) (Q) H37).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col D P Q) /\ ((euclidean__axioms.Col D Q P) /\ ((euclidean__axioms.Col Q P D) /\ ((euclidean__axioms.Col P Q D) /\ (euclidean__axioms.Col Q D P))))) as H39.
---------------------------- exact H38.
---------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col D Q P) /\ ((euclidean__axioms.Col Q P D) /\ ((euclidean__axioms.Col P Q D) /\ (euclidean__axioms.Col Q D P)))) as H41.
----------------------------- exact H40.
----------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col Q P D) /\ ((euclidean__axioms.Col P Q D) /\ (euclidean__axioms.Col Q D P))) as H43.
------------------------------ exact H42.
------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col P Q D) /\ (euclidean__axioms.Col Q D P)) as H45.
------------------------------- exact H44.
------------------------------- destruct H45 as [H45 H46].
exact H45.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong H E B C) as H39.
--------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (H) (B) (C) (E) H0).
--------------------------- assert (* Cut *) (euclidean__axioms.Col C B H) as H40.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col C B H) /\ ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))))) as H40.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (H) H4).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B H) /\ ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B)))) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B)) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
exact H41.
---------------------------- assert (* Cut *) (euclidean__axioms.Col C B E) as H41.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H41.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H5).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H42.
------------------------------- exact H41.
------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H44.
-------------------------------- exact H43.
-------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H46.
--------------------------------- exact H45.
--------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H48.
---------------------------------- exact H47.
---------------------------------- destruct H48 as [H48 H49].
exact H42.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H42.
------------------------------ exact H2.
------------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H43.
------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H43.
-------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H42).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H50.
------------------------------------ exact H49.
------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H52.
------------------------------------- exact H51.
------------------------------------- destruct H52 as [H52 H53].
exact H46.
------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H44.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H43).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B H E) as H45.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (H) (E)).
----------------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False (B) (H) (E) (H45)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (H) (E) (H40) (H41) H44).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col H E B) as H46.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col H B E) /\ ((euclidean__axioms.Col H E B) /\ ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B E H) /\ (euclidean__axioms.Col E H B))))) as H46.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (H) (E) H45).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H B E) /\ ((euclidean__axioms.Col H E B) /\ ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B E H) /\ (euclidean__axioms.Col E H B))))) as H47.
------------------------------------ exact H46.
------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col H E B) /\ ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B E H) /\ (euclidean__axioms.Col E H B)))) as H49.
------------------------------------- exact H48.
------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B E H) /\ (euclidean__axioms.Col E H B))) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col B E H) /\ (euclidean__axioms.Col E H B)) as H53.
--------------------------------------- exact H52.
--------------------------------------- destruct H53 as [H53 H54].
exact H49.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B C H) as H47.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H B) /\ ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B H E) /\ ((euclidean__axioms.Col H B E) /\ (euclidean__axioms.Col B E H))))) as H47.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (H) (E) (B) H46).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col E H B) /\ ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B H E) /\ ((euclidean__axioms.Col H B E) /\ (euclidean__axioms.Col B E H))))) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col E B H) /\ ((euclidean__axioms.Col B H E) /\ ((euclidean__axioms.Col H B E) /\ (euclidean__axioms.Col B E H)))) as H50.
-------------------------------------- exact H49.
-------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B H E) /\ ((euclidean__axioms.Col H B E) /\ (euclidean__axioms.Col B E H))) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col H B E) /\ (euclidean__axioms.Col B E H)) as H54.
---------------------------------------- exact H53.
---------------------------------------- destruct H54 as [H54 H55].
exact H4.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H48.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C B H) /\ ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))))) as H48.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (H) H47).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B H) /\ ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))))) as H49.
-------------------------------------- exact H48.
-------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col C H B) /\ ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B)))) as H51.
--------------------------------------- exact H50.
--------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col H B C) /\ ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B))) as H53.
---------------------------------------- exact H52.
---------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col B H C) /\ (euclidean__axioms.Col H C B)) as H55.
----------------------------------------- exact H54.
----------------------------------------- destruct H55 as [H55 H56].
exact H5.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col C H E) as H49.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (H) (E)).
--------------------------------------intro H49.
apply (@euclidean__tactics.Col__nCol__False (C) (H) (E) (H49)).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (H) (E) (H47) (H48) H43).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col H E C) as H50.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H C E) /\ ((euclidean__axioms.Col H E C) /\ ((euclidean__axioms.Col E C H) /\ ((euclidean__axioms.Col C E H) /\ (euclidean__axioms.Col E H C))))) as H50.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (H) (E) H49).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H C E) /\ ((euclidean__axioms.Col H E C) /\ ((euclidean__axioms.Col E C H) /\ ((euclidean__axioms.Col C E H) /\ (euclidean__axioms.Col E H C))))) as H51.
---------------------------------------- exact H50.
---------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col H E C) /\ ((euclidean__axioms.Col E C H) /\ ((euclidean__axioms.Col C E H) /\ (euclidean__axioms.Col E H C)))) as H53.
----------------------------------------- exact H52.
----------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col E C H) /\ ((euclidean__axioms.Col C E H) /\ (euclidean__axioms.Col E H C))) as H55.
------------------------------------------ exact H54.
------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col C E H) /\ (euclidean__axioms.Col E H C)) as H57.
------------------------------------------- exact H56.
------------------------------------------- destruct H57 as [H57 H58].
exact H53.
-------------------------------------- assert (* Cut *) (euclidean__axioms.ET D H E D B C) as H51.
--------------------------------------- apply (@proposition__38.proposition__38 (D) (H) (E) (D) (B) (C) (P) (Q) (H36) (H38) (H38) (H39) (H46) H50).
--------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C D B C) as H52.
---------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (A) (B) (C) (D) (B) (C) (D) (H) (E) (H1) H51).
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H E D) as H53.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H53.
------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H42).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H54.
------------------------------------------- exact H53.
------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H56.
-------------------------------------------- exact H55.
-------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H58.
--------------------------------------------- exact H57.
--------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H60.
---------------------------------------------- exact H59.
---------------------------------------------- destruct H60 as [H60 H61].
exact H16.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H54.
------------------------------------------ apply (@euclidean__tactics.nCol__notCol (B) (C) (D)).
-------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (C) (D)).
--------------------------------------------apply (@lemma__NChelper.lemma__NChelper (H) (E) (D) (B) (C) (H53) (H46) (H50) H43).


------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol D B C) as H55.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H55.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (D) H54).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H56.
--------------------------------------------- exact H55.
--------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)))) as H58.
---------------------------------------------- exact H57.
---------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))) as H60.
----------------------------------------------- exact H59.
----------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)) as H62.
------------------------------------------------ exact H61.
------------------------------------------------ destruct H62 as [H62 H63].
exact H60.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle D B C) as H56.
-------------------------------------------- exact H55.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H57.
--------------------------------------------- apply (@proposition__39.proposition__39 (A) (B) (C) (D) (H42) (H56) (H6) (H52) H7).
--------------------------------------------- exact H57.
Qed.
