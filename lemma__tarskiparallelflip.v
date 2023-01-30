Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__tarskiparallelflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.TP A B C D) -> ((euclidean__defs.TP B A C D) /\ ((euclidean__defs.TP A B D C) /\ (euclidean__defs.TP B A D C))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H0.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H3.
----- exact H2.
----- destruct H3 as [H3 H4].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
split.
------- exact H1.
------- split.
-------- exact H3.
-------- split.
--------- exact H5.
--------- exact H6.
- assert (* Cut *) (euclidean__defs.OS D C A B) as H1.
-- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H7.
------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (C) (D) H6).
------ assert (* AndElim *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
exact H8.
-- assert (* Cut *) (euclidean__axioms.neq D C) as H2.
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H4).
--- assert (* Cut *) (~(euclidean__defs.Meet A B D C)) as H3.
---- intro H3.
assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T)))) as H4.
----- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)))) as H4.
------ exact H0.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
exact H3.
----- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T))))) as H5.
------ exact H4.
------ destruct H5 as [T H5].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T)))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H12.
---------- exact H0.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* Cut *) (euclidean__axioms.Col C D T) as H18.
------------- assert (* Cut *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H18.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (T) H11).
-------------- assert (* AndElim *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D)))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D)) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
exact H19.
------------- assert (* Cut *) (euclidean__axioms.neq C D) as H19.
-------------- exact H14.
-------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H20.
--------------- exists T.
split.
---------------- exact H6.
---------------- split.
----------------- exact H19.
----------------- split.
------------------ exact H10.
------------------ exact H18.
--------------- apply (@H16 H20).
---- assert (* Cut *) (euclidean__defs.TP A B D C) as H4.
----- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H4.
------ exact H0.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
split.
--------- exact H4.
--------- split.
---------- exact H2.
---------- split.
----------- intro H10.
assert (* Cut *) (False) as H11.
------------ apply (@H3 H10).
------------ assert False.
-------------exact H11.
------------- contradiction.
----------- exact H1.
----- assert (* Cut *) (~(euclidean__defs.Meet B A C D)) as H5.
------ intro H5.
assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T)))) as H6.
------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)))) as H6.
-------- exact H0.
-------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
exact H5.
------- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T))))) as H7.
-------- exact H6.
-------- destruct H7 as [T H7].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T)))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T)) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H14.
------------ exact H0.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.Col A B T) as H20.
--------------- assert (* Cut *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H20.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (T) H12).
---------------- assert (* AndElim *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B)))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
exact H21.
--------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H21.
---------------- exists T.
split.
----------------- exact H14.
----------------- split.
------------------ exact H10.
------------------ split.
------------------- exact H20.
------------------- exact H13.
---------------- apply (@H18 H21).
------ assert (* Cut *) (euclidean__axioms.neq B A) as H6.
------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H6.
-------- exact H0.
-------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H6).
------- assert (* Cut *) (euclidean__defs.OS D C A B) as H7.
-------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H7.
--------- exact H0.
--------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H13.
------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (C) (D) H12).
------------ assert (* AndElim *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A)) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
exact H1.
-------- assert (* Cut *) (euclidean__defs.OS C D B A) as H8.
--------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H8.
---------- exact H0.
---------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H10.
----------- exact H9.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* Cut *) ((euclidean__defs.OS C D A B) /\ ((euclidean__defs.OS D C B A) /\ (euclidean__defs.OS C D B A))) as H14.
------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (D) (C) H7).
------------- assert (* AndElim *) ((euclidean__defs.OS C D A B) /\ ((euclidean__defs.OS D C B A) /\ (euclidean__defs.OS C D B A))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.OS D C B A) /\ (euclidean__defs.OS C D B A)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
exact H18.
--------- assert (* Cut *) (euclidean__defs.OS D C B A) as H9.
---------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H9.
----------- exact H0.
----------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H11.
------------ exact H10.
------------ destruct H11 as [H11 H12].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* Cut *) ((euclidean__defs.OS D C B A) /\ ((euclidean__defs.OS C D A B) /\ (euclidean__defs.OS D C A B))) as H15.
-------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (A) (C) (D) H8).
-------------- assert (* AndElim *) ((euclidean__defs.OS D C B A) /\ ((euclidean__defs.OS C D A B) /\ (euclidean__defs.OS D C A B))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.OS C D A B) /\ (euclidean__defs.OS D C A B)) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
exact H16.
---------- assert (* Cut *) (euclidean__defs.TP B A C D) as H10.
----------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H10.
------------ exact H0.
------------ destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H12.
------------- exact H11.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
split.
--------------- exact H6.
--------------- split.
---------------- exact H12.
---------------- split.
----------------- intro H16.
assert (* Cut *) (False) as H17.
------------------ apply (@H5 H16).
------------------ assert False.
-------------------exact H17.
------------------- contradiction.
----------------- exact H8.
----------- assert (* Cut *) (~(euclidean__defs.Meet B A D C)) as H11.
------------ intro H11.
assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T)))) as H12.
------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)))) as H12.
-------------- exact H0.
-------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B))) as H14.
--------------- exact H13.
--------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((~(exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.Col C D X))))) /\ (euclidean__defs.OS C D A B)) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
exact H11.
------------- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T))))) as H13.
-------------- exact H12.
-------------- destruct H13 as [T H13].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T)))) as H14.
--------------- exact H13.
--------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T)) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H20.
------------------ exact H0.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Col A B T) as H26.
--------------------- assert (* Cut *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H26.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (T) H18).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H27.
--------------------- assert (* Cut *) (euclidean__axioms.Col C D T) as H27.
---------------------- assert (* Cut *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H27.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (T) H19).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D)))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D)) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
exact H28.
---------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H28.
----------------------- exists T.
split.
------------------------ exact H20.
------------------------ split.
------------------------- exact H22.
------------------------- split.
-------------------------- exact H26.
-------------------------- exact H27.
----------------------- apply (@H24 H28).
------------ assert (* Cut *) (euclidean__defs.TP B A D C) as H12.
------------- split.
-------------- exact H6.
-------------- split.
--------------- exact H2.
--------------- split.
---------------- exact H11.
---------------- exact H9.
------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point) (P: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C P Q) /\ ((euclidean__axioms.BetS D R Q) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H13.
-------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))))) as H13.
--------------- exact H0.
--------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))))) as H15.
---------------- exact H14.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
exact H18.
-------------- assert (exists Q: euclidean__axioms.Point, (exists (P: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C P Q) /\ ((euclidean__axioms.BetS D R Q) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H14.
--------------- exact H13.
--------------- destruct H14 as [P H14].
assert (exists P0: euclidean__axioms.Point, (exists (R: euclidean__axioms.Point), (euclidean__axioms.Col A B P0) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C P0 P) /\ ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H15.
---------------- exact H14.
---------------- destruct H15 as [Q H15].
assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C Q P) /\ ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H16.
----------------- exact H15.
----------------- destruct H16 as [R H16].
assert (* AndElim *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C Q P) /\ ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H17.
------------------ exact H16.
------------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C Q P) /\ ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS C Q P) /\ ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS D R P) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H27.
----------------------- exact H0.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
split.
-------------------------- exact H10.
-------------------------- split.
--------------------------- exact H4.
--------------------------- exact H12.
Qed.
