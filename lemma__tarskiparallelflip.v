Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__tarskiparallelflip : forall A B C D, (euclidean__defs.TP A B C D) -> ((euclidean__defs.TP B A C D) /\ ((euclidean__defs.TP A B D C) /\ (euclidean__defs.TP B A D C))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H0.
- assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H0 by exact H.
assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
split.
-- exact H1.
-- split.
--- exact H3.
--- split.
---- exact H5.
---- exact H6.
- assert (* Cut *) (euclidean__defs.OS D C A B) as H1.
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H7.
--- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B C D H6).
--- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H8.
-- assert (* Cut *) (euclidean__axioms.neq D C) as H2.
--- destruct H0 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H4).
--- assert (* Cut *) (~(euclidean__defs.Meet A B D C)) as H3.
---- intro H3.
assert (* Cut *) (exists T, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col D C T)))) as H4.
----- destruct H0 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H3.
----- destruct H4 as [T H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H0 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
assert (* Cut *) (euclidean__axioms.Col C D T) as H18.
------ assert (* Cut *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H18.
------- apply (@lemma__collinearorder.lemma__collinearorder D C T H11).
------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
------ assert (euclidean__axioms.neq C D) as H19 by exact H14.
assert (* Cut *) (euclidean__defs.Meet A B C D) as H20.
------- exists T.
split.
-------- exact H6.
-------- split.
--------- exact H19.
--------- split.
---------- exact H10.
---------- exact H18.
------- apply (@H16 H20).
---- assert (* Cut *) (euclidean__defs.TP A B D C) as H4.
----- destruct H0 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
split.
------ exact H4.
------ split.
------- exact H2.
------- split.
-------- intro H10.
assert (* Cut *) (False) as H11.
--------- apply (@H3 H10).
--------- contradiction H11.
-------- exact H1.
----- assert (* Cut *) (~(euclidean__defs.Meet B A C D)) as H5.
------ intro H5.
assert (* Cut *) (exists T, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col C D T)))) as H6.
------- destruct H0 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H5.
------- destruct H6 as [T H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H0 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
assert (* Cut *) (euclidean__axioms.Col A B T) as H20.
-------- assert (* Cut *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H20.
--------- apply (@lemma__collinearorder.lemma__collinearorder B A T H12).
--------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
-------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H21.
--------- exists T.
split.
---------- exact H14.
---------- split.
----------- exact H10.
----------- split.
------------ exact H20.
------------ exact H13.
--------- apply (@H18 H21).
------ assert (* Cut *) (euclidean__axioms.neq B A) as H6.
------- destruct H0 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H6).
------- assert (* Cut *) (euclidean__defs.OS D C A B) as H7.
-------- destruct H0 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H13.
--------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B C D H12).
--------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H1.
-------- assert (* Cut *) (euclidean__defs.OS C D B A) as H8.
--------- destruct H0 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
assert (* Cut *) ((euclidean__defs.OS C D A B) /\ ((euclidean__defs.OS D C B A) /\ (euclidean__defs.OS C D B A))) as H14.
---------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B D C H7).
---------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
--------- assert (* Cut *) (euclidean__defs.OS D C B A) as H9.
---------- destruct H0 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (* Cut *) ((euclidean__defs.OS D C B A) /\ ((euclidean__defs.OS C D A B) /\ (euclidean__defs.OS D C A B))) as H15.
----------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric B A C D H8).
----------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
---------- assert (* Cut *) (euclidean__defs.TP B A C D) as H10.
----------- destruct H0 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
split.
------------ exact H6.
------------ split.
------------- exact H12.
------------- split.
-------------- intro H16.
assert (* Cut *) (False) as H17.
--------------- apply (@H5 H16).
--------------- contradiction H17.
-------------- exact H8.
----------- assert (* Cut *) (~(euclidean__defs.Meet B A D C)) as H11.
------------ intro H11.
assert (* Cut *) (exists T, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A T) /\ (euclidean__axioms.Col D C T)))) as H12.
------------- destruct H0 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H11.
------------- destruct H12 as [T H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H0 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Col A B T) as H26.
-------------- assert (* Cut *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B T A) /\ (euclidean__axioms.Col T A B))))) as H26.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B A T H18).
--------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H27.
-------------- assert (* Cut *) (euclidean__axioms.Col C D T) as H27.
--------------- assert (* Cut *) ((euclidean__axioms.Col C D T) /\ ((euclidean__axioms.Col C T D) /\ ((euclidean__axioms.Col T D C) /\ ((euclidean__axioms.Col D T C) /\ (euclidean__axioms.Col T C D))))) as H27.
---------------- apply (@lemma__collinearorder.lemma__collinearorder D C T H19).
---------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H28.
--------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H28.
---------------- exists T.
split.
----------------- exact H20.
----------------- split.
------------------ exact H22.
------------------ split.
------------------- exact H26.
------------------- exact H27.
---------------- apply (@H24 H28).
------------ assert (* Cut *) (euclidean__defs.TP B A D C) as H12.
------------- split.
-------------- exact H6.
-------------- split.
--------------- exact H2.
--------------- split.
---------------- exact H11.
---------------- exact H9.
------------- assert (* Cut *) (exists Q P R, (euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.BetS C P Q) /\ ((euclidean__axioms.BetS D R Q) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H13.
-------------- destruct H0 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
-------------- destruct H13 as [P H14].
destruct H14 as [Q H15].
destruct H15 as [R H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H0 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
split.
--------------- exact H10.
--------------- split.
---------------- exact H4.
---------------- exact H12.
Qed.
