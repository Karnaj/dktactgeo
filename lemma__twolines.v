Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear1.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__twolines : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Cut A B C D E) -> ((euclidean__defs.Cut A B C D F) -> ((euclidean__axioms.nCol B C D) -> (E = F))).
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
assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H2.
- assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H2.
-- exact H0.
-- assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp.
--- exact H2.
--- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H9.
------- exact H.
------- assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp0.
-------- exact H9.
-------- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H10.
--------- exact __TmpHyp0.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
split.
------------ exact H10.
------------ split.
------------- exact H12.
------------- split.
-------------- exact H14.
-------------- exact H15.
- assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H3.
-- assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H3.
--- exact H2.
--- assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp.
---- exact H3.
---- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H4.
----- exact __TmpHyp.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H10.
-------- exact H0.
-------- assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp0.
--------- exact H10.
--------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H11.
---------- exact __TmpHyp0.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H17.
------------- exact H.
------------- assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp1.
-------------- exact H17.
-------------- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H18.
--------------- exact __TmpHyp1.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
split.
------------------ exact H11.
------------------ split.
------------------- exact H13.
------------------- split.
-------------------- exact H22.
-------------------- exact H23.
-- assert (* Cut *) (euclidean__axioms.Col A E B) as H4.
--- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H4.
---- exact H2.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H6.
----- exact H3.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H8.
------ exact H5.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H10.
------- exact H7.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H12.
-------- exact H9.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H14.
--------- exact H11.
--------- destruct H14 as [H14 H15].
right.
right.
right.
right.
left.
exact H4.
--- assert (* Cut *) (euclidean__axioms.Col A B E) as H5.
---- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H5.
----- exact H3.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H11.
-------- exact H2.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H17.
----------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H4).
----------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
exact H24.
---- assert (* Cut *) (euclidean__axioms.Col A F B) as H6.
----- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H6.
------ exact H2.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H8.
------- exact H3.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H10.
-------- exact H7.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H12.
--------- exact H9.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H14.
---------- exact H11.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H16.
----------- exact H13.
----------- destruct H16 as [H16 H17].
right.
right.
right.
right.
left.
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col A B F) as H7.
------ assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H7.
------- exact H3.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H13.
---------- exact H2.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H19.
------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (B) H6).
------------- assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A)))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A)) as H26.
----------------- exact H25.
----------------- destruct H26 as [H26 H27].
exact H26.
------ assert (* Cut *) (euclidean__axioms.neq A B) as H8.
------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H8.
-------- exact H3.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H14.
----------- exact H2.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A B))) as H20.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (F) (B) H8).
-------------- assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A B))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A B)) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
exact H24.
------- assert (* Cut *) (euclidean__axioms.Col B E F) as H9.
-------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H9.
--------- exact H3.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H15.
------------ exact H2.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
apply (@euclidean__tactics.not__nCol__Col (B) (E) (F)).
---------------intro H21.
apply (@euclidean__tactics.Col__nCol__False (B) (E) (F) (H21)).
----------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (E) (F) (H5) (H7) H8).


-------- assert (* Cut *) (euclidean__axioms.Col E F B) as H10.
--------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H10.
---------- exact H3.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H16.
------------- exact H2.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H22.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (F) H9).
---------------- assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)))) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)) as H29.
-------------------- exact H28.
-------------------- destruct H29 as [H29 H30].
exact H25.
--------- assert (* Cut *) (euclidean__axioms.Col C E D) as H11.
---------- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H11.
----------- exact H2.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H13.
------------ exact H3.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H15.
------------- exact H12.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H17.
-------------- exact H14.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H19.
--------------- exact H16.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H21.
---------------- exact H18.
---------------- destruct H21 as [H21 H22].
right.
right.
right.
right.
left.
exact H15.
---------- assert (* Cut *) (euclidean__axioms.Col C F D) as H12.
----------- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H12.
------------ exact H2.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H14.
------------- exact H3.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H16.
-------------- exact H13.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H18.
--------------- exact H15.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H20.
---------------- exact H17.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H22.
----------------- exact H19.
----------------- destruct H22 as [H22 H23].
right.
right.
right.
right.
left.
exact H18.
----------- assert (* Cut *) (euclidean__axioms.Col C D F) as H13.
------------ assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H13.
------------- exact H3.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H19.
---------------- exact H2.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H25.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H12).
------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
exact H32.
------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H14.
------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H14.
-------------- exact H3.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H20.
----------------- exact H2.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H26.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (D) H11).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
exact H33.
------------- assert (* Cut *) (euclidean__axioms.neq C D) as H15.
-------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H15.
--------------- exact H3.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H21.
------------------ exact H2.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H27.
--------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (D) H17).
--------------------- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D)) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
exact H31.
-------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H16.
--------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H16.
---------------- exact H3.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H22.
------------------- exact H2.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
----------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H28)).
-----------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (E) (F) (H14) (H13) H15).


--------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H17.
---------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H17.
----------------- exact H3.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H23.
-------------------- exact H2.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H27.
---------------------- exact H26.
---------------------- destruct H27 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H29.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (F) H16).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D)))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D)) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
exact H32.
---------------- assert (* Cut *) (euclidean__axioms.Col D C E) as H18.
----------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H18.
------------------ exact H3.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H24.
--------------------- exact H2.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
apply (@lemma__collinear1.lemma__collinear1 (C) (D) (E) H14).
----------------- assert (* Cut *) (euclidean__axioms.Col D C F) as H19.
------------------ assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H19.
------------------- exact H3.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H25.
---------------------- exact H2.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
apply (@lemma__collinear1.lemma__collinear1 (C) (D) (F) H13).
------------------ assert (* Cut *) (euclidean__axioms.BetS D E C) as H20.
------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H20.
-------------------- exact H3.
-------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H22.
--------------------- exact H21.
--------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H26.
----------------------- exact H2.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (E) (D) H28).
------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H21.
-------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H21.
--------------------- exact H3.
--------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H23.
---------------------- exact H22.
---------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H27.
------------------------ exact H2.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq D E) /\ (euclidean__axioms.neq D C))) as H33.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (E) (C) H20).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq D E) /\ (euclidean__axioms.neq D C))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ (euclidean__axioms.neq D C)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H37.
-------------------- assert (* Cut *) (euclidean__axioms.Col C E F) as H22.
--------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H22.
---------------------- exact H3.
---------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H24.
----------------------- exact H23.
----------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H28.
------------------------- exact H2.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
apply (@euclidean__tactics.not__nCol__Col (C) (E) (F)).
----------------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False (C) (E) (F) (H34)).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (E) (F) (H18) (H19) H21).


--------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H23.
---------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H23.
----------------------- exact H3.
----------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H25.
------------------------ exact H24.
------------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H29.
-------------------------- exact H2.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))))) as H35.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (F) H22).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C)))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C)) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
exact H38.
---------------------- assert (* Cut *) (~(euclidean__axioms.neq E F)) as H24.
----------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col F B C) as H25.
------------------------ assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H25.
------------------------- exact H3.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H31.
---------------------------- exact H2.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
apply (@euclidean__tactics.not__nCol__Col (F) (B) (C)).
-------------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False (F) (B) (C) (H37)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (F) (B) (C) (H10) (H23) H24).


------------------------ assert (* Cut *) (euclidean__axioms.Col F B D) as H26.
------------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H26.
-------------------------- exact H3.
-------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H32.
----------------------------- exact H2.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
apply (@euclidean__tactics.not__nCol__Col (F) (B) (D)).
--------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (F) (B) (D) (H38)).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (F) (B) (D) (H10) (H17) H24).


------------------------- assert (* Cut *) (~(F = B)) as H27.
-------------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col F C D) as H28.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H28.
---------------------------- exact H2.
---------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H30.
----------------------------- exact H3.
----------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H32.
------------------------------ exact H29.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H34.
------------------------------- exact H31.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H36.
-------------------------------- exact H33.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H38.
--------------------------------- exact H35.
--------------------------------- destruct H38 as [H38 H39].
right.
right.
right.
left.
exact H34.
--------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H29.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H29.
----------------------------- exact H3.
----------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H31.
------------------------------ exact H30.
------------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H35.
-------------------------------- exact H2.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.Cut A B C D F0) -> ((euclidean__axioms.BetS A F0 B) -> ((euclidean__axioms.BetS C F0 D) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__axioms.Col B E F0) -> ((euclidean__axioms.Col E F0 B) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.Col C D F0) -> ((euclidean__axioms.Col D E F0) -> ((euclidean__axioms.Col E F0 D) -> ((euclidean__axioms.Col D C F0) -> ((euclidean__axioms.Col C E F0) -> ((euclidean__axioms.Col E F0 C) -> ((euclidean__axioms.neq E F0) -> ((euclidean__axioms.Col F0 B C) -> ((euclidean__axioms.Col F0 B D) -> ((euclidean__axioms.Col F0 C D) -> (euclidean__axioms.Col B C D)))))))))))))))))))) with (x := F).
-----------------------------------intro H41.
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
intro H57.
intro H58.
exact H58.

----------------------------------- exact H27.
----------------------------------- exact H0.
----------------------------------- exact H29.
----------------------------------- exact H31.
----------------------------------- exact H6.
----------------------------------- exact H7.
----------------------------------- exact H9.
----------------------------------- exact H10.
----------------------------------- exact H12.
----------------------------------- exact H13.
----------------------------------- exact H16.
----------------------------------- exact H17.
----------------------------------- exact H19.
----------------------------------- exact H22.
----------------------------------- exact H23.
----------------------------------- exact H24.
----------------------------------- exact H25.
----------------------------------- exact H26.
----------------------------------- exact H28.
---------------------------- apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H1) H29).
-------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H28.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H28.
---------------------------- exact H3.
---------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H34.
------------------------------- exact H2.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
apply (@euclidean__tactics.not__nCol__Col (B) (C) (D)).
----------------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H40)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (B) (C) (D) (H25) (H26) H27).


--------------------------- apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H1) H28).
----------------------- apply (@euclidean__tactics.NNPP (E = F)).
------------------------intro H25.
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS B C D)) /\ ((~(euclidean__axioms.BetS B D C)) /\ (~(euclidean__axioms.BetS C B D))))))) as H26.
------------------------- exact H1.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))))))) as H28.
-------------------------- exact H2.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))))))) as H30.
--------------------------- exact H3.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS B C D)) /\ ((~(euclidean__axioms.BetS B D C)) /\ (~(euclidean__axioms.BetS C B D)))))) as H32.
---------------------------- exact H27.
---------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))))) as H34.
----------------------------- exact H29.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.BetS C F D) /\ (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))))) as H36.
------------------------------ exact H31.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS B C D)) /\ ((~(euclidean__axioms.BetS B D C)) /\ (~(euclidean__axioms.BetS C B D))))) as H38.
------------------------------- exact H33.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))))) as H40.
-------------------------------- exact H35.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) (((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))))) as H42.
--------------------------------- exact H37.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C D)) /\ ((~(euclidean__axioms.BetS B D C)) /\ (~(euclidean__axioms.BetS C B D)))) as H44.
---------------------------------- exact H39.
---------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H46.
----------------------------------- exact H40.
----------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H48.
------------------------------------ exact H41.
------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H50.
------------------------------------- exact H42.
------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H52.
-------------------------------------- exact H43.
-------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D C)) /\ (~(euclidean__axioms.BetS C B D))) as H54.
--------------------------------------- exact H45.
--------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H56.
---------------------------------------- exact H47.
---------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H58.
----------------------------------------- exact H49.
----------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H60.
------------------------------------------ exact H51.
------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H62.
------------------------------------------- exact H53.
------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H64.
-------------------------------------------- exact H57.
-------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H66.
--------------------------------------------- exact H59.
--------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H68.
---------------------------------------------- exact H61.
---------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H70.
----------------------------------------------- exact H63.
----------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H72.
------------------------------------------------ exact H65.
------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H74.
------------------------------------------------- exact H67.
------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H76.
-------------------------------------------------- exact H69.
-------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H78.
--------------------------------------------------- exact H71.
--------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H80.
---------------------------------------------------- exact H73.
---------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H82.
----------------------------------------------------- exact H75.
----------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H84.
------------------------------------------------------ exact H77.
------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H86.
------------------------------------------------------- exact H79.
------------------------------------------------------- destruct H86 as [H86 H87].
assert (* Cut *) (False) as H88.
-------------------------------------------------------- apply (@H24 H25).
-------------------------------------------------------- assert False.
---------------------------------------------------------exact H88.
--------------------------------------------------------- contradiction.

Qed.
