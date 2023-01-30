Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export logic.
Definition lemma__collinearparallel2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__axioms.Col C D E) -> ((euclidean__axioms.Col C D F) -> ((euclidean__axioms.neq E F) -> (euclidean__defs.Par A B E F)))).
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
assert (* Cut *) (euclidean__axioms.neq F E) as H3.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H2).
- assert (* Cut *) (euclidean__axioms.nCol A C D) as H4.
-- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H4.
--- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H).
--- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
exact H7.
-- assert (* Cut *) (euclidean__axioms.neq C D) as H5.
--- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H5.
---- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (D) H4).
---- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
exact H8.
--- assert (* Cut *) (euclidean__axioms.neq D C) as H6.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H5).
---- assert (* Cut *) (euclidean__axioms.Col D C E) as H7.
----- assert (* Cut *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C))))) as H7.
------ apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (E) H0).
------ assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C)))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C)) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col D C F) as H8.
------ assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H8.
------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (F) H1).
------- assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H9.
------ assert (* Cut *) (euclidean__axioms.Col C E F) as H9.
------- apply (@euclidean__tactics.not__nCol__Col (C) (E) (F)).
--------intro H9.
apply (@euclidean__tactics.Col__nCol__False (C) (E) (F) (H9)).
---------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (E) (F) (H7) (H8) H6).


------- assert (* Cut *) (euclidean__axioms.Col C F E) as H10.
-------- assert (* Cut *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))))) as H10.
--------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (F) H9).
--------- assert (* AndElim *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C)))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C)) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
exact H17.
-------- assert (* Cut *) (euclidean__defs.Par A B D C) as H11.
--------- assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H11.
---------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H).
---------- assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
exact H14.
--------- assert (* Cut *) (euclidean__defs.Par A B E F) as H12.
---------- assert (* Cut *) ((E = D) \/ (euclidean__axioms.neq E D)) as H12.
----------- apply (@euclidean__tactics.eq__or__neq (E) D).
----------- assert (* Cut *) ((E = D) \/ (euclidean__axioms.neq E D)) as H13.
------------ exact H12.
------------ assert (* Cut *) ((E = D) \/ (euclidean__axioms.neq E D)) as __TmpHyp.
------------- exact H13.
------------- assert (E = D \/ euclidean__axioms.neq E D) as H14.
-------------- exact __TmpHyp.
-------------- destruct H14 as [H14|H14].
--------------- assert (* Cut *) (euclidean__axioms.neq D F) as H15.
---------------- apply (@eq__ind__r euclidean__axioms.Point D (fun E0: euclidean__axioms.Point => (euclidean__axioms.Col C D E0) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col D C E0) -> ((euclidean__axioms.Col C E0 F) -> ((euclidean__axioms.Col C F E0) -> (euclidean__axioms.neq D F)))))))) with (x := E).
-----------------intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
exact H16.

----------------- exact H14.
----------------- exact H0.
----------------- exact H2.
----------------- exact H3.
----------------- exact H7.
----------------- exact H9.
----------------- exact H10.
---------------- assert (* Cut *) (euclidean__axioms.neq F D) as H16.
----------------- apply (@eq__ind__r euclidean__axioms.Point D (fun E0: euclidean__axioms.Point => (euclidean__axioms.Col C D E0) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col D C E0) -> ((euclidean__axioms.Col C E0 F) -> ((euclidean__axioms.Col C F E0) -> (euclidean__axioms.neq F D)))))))) with (x := E).
------------------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
exact H18.

------------------ exact H14.
------------------ exact H0.
------------------ exact H2.
------------------ exact H3.
------------------ exact H7.
------------------ exact H9.
------------------ exact H10.
----------------- assert (* Cut *) (euclidean__defs.Par A B F D) as H17.
------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (F) (C) (D) (H) (H1) H16).
------------------ assert (* Cut *) (euclidean__defs.Par A B D F) as H18.
------------------- assert (* Cut *) ((euclidean__defs.Par B A F D) /\ ((euclidean__defs.Par A B D F) /\ (euclidean__defs.Par B A D F))) as H18.
-------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (F) (D) H17).
-------------------- assert (* AndElim *) ((euclidean__defs.Par B A F D) /\ ((euclidean__defs.Par A B D F) /\ (euclidean__defs.Par B A D F))) as H19.
--------------------- exact H18.
--------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Par A B D F) /\ (euclidean__defs.Par B A D F)) as H21.
---------------------- exact H20.
---------------------- destruct H21 as [H21 H22].
exact H21.
------------------- assert (* Cut *) (euclidean__axioms.Col C F D) as H19.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))))) as H19.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (F) H8).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))))) as H20.
---------------------- exact H19.
---------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D)))) as H22.
----------------------- exact H21.
----------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ (euclidean__axioms.Col F C D)) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
exact H22.
-------------------- assert (* Cut *) (euclidean__axioms.Col C F E) as H20.
--------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H20.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H19).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H21.
----------------------- exact H20.
----------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H23.
------------------------ exact H22.
------------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
exact H10.
--------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H21.
---------------------- assert (* Cut *) ((C = F) \/ (euclidean__axioms.neq C F)) as H21.
----------------------- apply (@euclidean__tactics.eq__or__neq (C) F).
----------------------- assert (* Cut *) ((C = F) \/ (euclidean__axioms.neq C F)) as H22.
------------------------ exact H21.
------------------------ assert (* Cut *) ((C = F) \/ (euclidean__axioms.neq C F)) as __TmpHyp0.
------------------------- exact H22.
------------------------- assert (C = F \/ euclidean__axioms.neq C F) as H23.
-------------------------- exact __TmpHyp0.
-------------------------- destruct H23 as [H23|H23].
--------------------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H24.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))))) as H24.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (E) H20).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))))) as H25.
------------------------------ exact H24.
------------------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C)))) as H27.
------------------------------- exact H26.
------------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))) as H29.
-------------------------------- exact H28.
-------------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C)) as H31.
--------------------------------- exact H30.
--------------------------------- destruct H31 as [H31 H32].
exact H0.
---------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H25.
----------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun C0: euclidean__axioms.Point => (euclidean__defs.Par A B C0 D) -> ((euclidean__axioms.Col C0 D E) -> ((euclidean__axioms.Col C0 D F) -> ((euclidean__axioms.nCol A C0 D) -> ((euclidean__axioms.neq C0 D) -> ((euclidean__axioms.neq D C0) -> ((euclidean__axioms.Col D C0 E) -> ((euclidean__axioms.Col D C0 F) -> ((euclidean__axioms.Col C0 E F) -> ((euclidean__axioms.Col C0 F E) -> ((euclidean__defs.Par A B D C0) -> ((euclidean__axioms.Col C0 F D) -> ((euclidean__axioms.Col C0 F E) -> ((euclidean__axioms.Col C0 D E) -> (euclidean__axioms.Col F D E)))))))))))))))) with (x := C).
------------------------------intro H25.
intro H26.
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
apply (@eq__ind__r euclidean__axioms.Point D (fun E0: euclidean__axioms.Point => (euclidean__axioms.Col F D E0) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col F F E0) -> ((euclidean__axioms.Col F E0 F) -> ((euclidean__axioms.Col D F E0) -> ((euclidean__axioms.Col F F E0) -> ((euclidean__axioms.Col F D E0) -> (euclidean__axioms.Col F D E0)))))))))) with (x := E).
-------------------------------intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
exact H46.

------------------------------- exact H14.
------------------------------- exact H26.
------------------------------- exact H2.
------------------------------- exact H3.
------------------------------- exact H34.
------------------------------- exact H33.
------------------------------- exact H31.
------------------------------- exact H37.
------------------------------- exact H38.

------------------------------ exact H23.
------------------------------ exact H.
------------------------------ exact H0.
------------------------------ exact H1.
------------------------------ exact H4.
------------------------------ exact H5.
------------------------------ exact H6.
------------------------------ exact H7.
------------------------------ exact H8.
------------------------------ exact H9.
------------------------------ exact H10.
------------------------------ exact H11.
------------------------------ exact H19.
------------------------------ exact H20.
------------------------------ exact H24.
----------------------------- exact H25.
--------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H24.
---------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (D) (E)).
-----------------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False (F) (D) (E) (H24)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (F) (D) (E) (H19) (H20) H23).


---------------------------- exact H24.
---------------------- assert (* Cut *) (euclidean__axioms.Col D F E) as H22.
----------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H22.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (D) (E) H21).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H23.
------------------------- exact H22.
------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)))) as H25.
-------------------------- exact H24.
-------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))) as H27.
--------------------------- exact H26.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
exact H23.
----------------------- assert (* Cut *) (euclidean__defs.Par A B E F) as H23.
------------------------ apply (@eq__ind__r euclidean__axioms.Point D (fun E0: euclidean__axioms.Point => (euclidean__axioms.Col C D E0) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col D C E0) -> ((euclidean__axioms.Col C E0 F) -> ((euclidean__axioms.Col C F E0) -> ((euclidean__axioms.Col C F E0) -> ((euclidean__axioms.Col F D E0) -> ((euclidean__axioms.Col D F E0) -> (euclidean__defs.Par A B E0 F))))))))))) with (x := E).
-------------------------intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
exact H18.

------------------------- exact H14.
------------------------- exact H0.
------------------------- exact H2.
------------------------- exact H3.
------------------------- exact H7.
------------------------- exact H9.
------------------------- exact H10.
------------------------- exact H20.
------------------------- exact H21.
------------------------- exact H22.
------------------------ exact H23.
--------------- assert (* Cut *) (euclidean__defs.Par A B E D) as H15.
---------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (E) (C) (D) (H) (H0) H14).
---------------- assert (* Cut *) (euclidean__defs.Par A B D E) as H16.
----------------- assert (* Cut *) ((euclidean__defs.Par B A E D) /\ ((euclidean__defs.Par A B D E) /\ (euclidean__defs.Par B A D E))) as H16.
------------------ apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (E) (D) H15).
------------------ assert (* AndElim *) ((euclidean__defs.Par B A E D) /\ ((euclidean__defs.Par A B D E) /\ (euclidean__defs.Par B A D E))) as H17.
------------------- exact H16.
------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Par A B D E) /\ (euclidean__defs.Par B A D E)) as H19.
-------------------- exact H18.
-------------------- destruct H19 as [H19 H20].
exact H19.
----------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H17.
------------------ apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
-------------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H17)).
--------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (E) (F) (H0) (H1) H5).


------------------ assert (* Cut *) (euclidean__defs.Par A B F E) as H18.
------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (F) (D) (E) (H16) (H17) H3).
------------------- assert (* Cut *) (euclidean__defs.Par A B E F) as H19.
-------------------- assert (* Cut *) ((euclidean__defs.Par B A F E) /\ ((euclidean__defs.Par A B E F) /\ (euclidean__defs.Par B A E F))) as H19.
--------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (F) (E) H18).
--------------------- assert (* AndElim *) ((euclidean__defs.Par B A F E) /\ ((euclidean__defs.Par A B E F) /\ (euclidean__defs.Par B A E F))) as H20.
---------------------- exact H19.
---------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Par A B E F) /\ (euclidean__defs.Par B A E F)) as H22.
----------------------- exact H21.
----------------------- destruct H22 as [H22 H23].
exact H22.
-------------------- exact H19.
---------- exact H12.
Qed.
