Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__collinearbetween : forall A B C D E F H, (euclidean__axioms.Col A E B) -> ((euclidean__axioms.Col C F D) -> ((euclidean__axioms.neq A B) -> ((euclidean__axioms.neq C D) -> ((euclidean__axioms.neq A E) -> ((euclidean__axioms.neq F D) -> ((~(euclidean__defs.Meet A B C D)) -> ((euclidean__axioms.BetS A H D) -> ((euclidean__axioms.Col E F H) -> (euclidean__axioms.BetS E H F))))))))).
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
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
intro H8.
assert (* Cut *) (~(H = E)) as H9.
- intro H9.
assert (* Cut *) (euclidean__axioms.Col A H B) as H10.
-- apply (@eq__ind__r euclidean__axioms.Point E (fun H10 => (euclidean__axioms.BetS A H10 D) -> ((euclidean__axioms.Col E F H10) -> (euclidean__axioms.Col A H10 B)))) with (x := H).
---intro H10.
intro H11.
exact H0.

--- exact H9.
--- exact H7.
--- exact H8.
-- assert (* Cut *) (euclidean__axioms.Col H A B) as H11.
--- assert (* Cut *) ((euclidean__axioms.Col H A B) /\ ((euclidean__axioms.Col H B A) /\ ((euclidean__axioms.Col B A H) /\ ((euclidean__axioms.Col A B H) /\ (euclidean__axioms.Col B H A))))) as H11.
---- apply (@lemma__collinearorder.lemma__collinearorder A H B H10).
---- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H12.
--- assert (* Cut *) (euclidean__axioms.Col A H D) as H12.
---- right.
right.
right.
right.
left.
exact H7.
---- assert (* Cut *) (euclidean__axioms.Col H A D) as H13.
----- assert (* Cut *) ((euclidean__axioms.Col H A D) /\ ((euclidean__axioms.Col H D A) /\ ((euclidean__axioms.Col D A H) /\ ((euclidean__axioms.Col A D H) /\ (euclidean__axioms.Col D H A))))) as H13.
------ apply (@lemma__collinearorder.lemma__collinearorder A H D H12).
------ destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H14.
----- assert (* Cut *) (euclidean__axioms.neq A H) as H14.
------ assert (* Cut *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq A H) /\ (euclidean__axioms.neq A D))) as H14.
------- apply (@lemma__betweennotequal.lemma__betweennotequal A H D H7).
------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H17.
------ assert (* Cut *) (euclidean__axioms.neq H A) as H15.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A H H14).
------- assert (* Cut *) (euclidean__axioms.Col A B D) as H16.
-------- apply (@euclidean__tactics.not__nCol__Col A B D).
---------intro H16.
apply (@euclidean__tactics.Col__nCol__False A B D H16).
----------apply (@lemma__collinear4.lemma__collinear4 H A B D H11 H13 H15).


-------- assert (* Cut *) (D = D) as H17.
--------- apply (@logic.eq__refl Point D).
--------- assert (* Cut *) (euclidean__axioms.Col C D D) as H18.
---------- right.
right.
left.
exact H17.
---------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H19.
----------- exists D.
split.
------------ exact H2.
------------ split.
------------- exact H3.
------------- split.
-------------- exact H16.
-------------- exact H18.
----------- apply (@H6 H19).
- assert (* Cut *) (~(H = F)) as H10.
-- intro H10.
assert (* Cut *) (euclidean__axioms.Col A H D) as H11.
--- right.
right.
right.
right.
left.
exact H7.
--- assert (* Cut *) (euclidean__axioms.Col A F D) as H12.
---- apply (@eq__ind__r euclidean__axioms.Point F (fun H12 => (euclidean__axioms.BetS A H12 D) -> ((euclidean__axioms.Col E F H12) -> ((~(H12 = E)) -> ((euclidean__axioms.Col A H12 D) -> (euclidean__axioms.Col A F D)))))) with (x := H).
-----intro H12.
intro H13.
intro H14.
intro H15.
exact H15.

----- exact H10.
----- exact H7.
----- exact H8.
----- exact H9.
----- exact H11.
---- assert (* Cut *) (euclidean__axioms.Col F D A) as H13.
----- assert (* Cut *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col F D A) /\ ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A))))) as H13.
------ apply (@lemma__collinearorder.lemma__collinearorder A F D H12).
------ destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H16.
----- assert (* Cut *) (euclidean__axioms.Col F D C) as H14.
------ assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H14.
------- apply (@lemma__collinearorder.lemma__collinearorder C F D H1).
------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H17.
------ assert (* Cut *) (euclidean__axioms.Col D A C) as H15.
------- apply (@euclidean__tactics.not__nCol__Col D A C).
--------intro H15.
apply (@euclidean__tactics.Col__nCol__False D A C H15).
---------apply (@lemma__collinear4.lemma__collinear4 F D A C H13 H14 H5).


------- assert (* Cut *) (euclidean__axioms.Col C D A) as H16.
-------- assert (* Cut *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D C A) /\ (euclidean__axioms.Col C A D))))) as H16.
--------- apply (@lemma__collinearorder.lemma__collinearorder D A C H15).
--------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H21.
-------- assert (* Cut *) (A = A) as H17.
--------- apply (@logic.eq__refl Point A).
--------- assert (* Cut *) (euclidean__axioms.Col A B A) as H18.
---------- right.
left.
exact H17.
---------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H19.
----------- exists A.
split.
------------ exact H2.
------------ split.
------------- exact H3.
------------- split.
-------------- exact H18.
-------------- exact H16.
----------- apply (@H6 H19).
-- assert (* Cut *) (~(euclidean__axioms.BetS E F H)) as H11.
--- intro H11.
assert (* Cut *) (euclidean__axioms.BetS D H A) as H12.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry A H D H7).
---- assert (* Cut *) (~(euclidean__axioms.Col D A E)) as H13.
----- intro H13.
assert (* Cut *) (euclidean__axioms.Col E A B) as H14.
------ assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H14.
------- apply (@lemma__collinearorder.lemma__collinearorder A E B H0).
------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H15.
------ assert (* Cut *) (euclidean__axioms.Col E A D) as H15.
------- assert (* Cut *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D))))) as H15.
-------- apply (@lemma__collinearorder.lemma__collinearorder D A E H13).
-------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H23.
------- assert (* Cut *) (euclidean__axioms.neq E A) as H16.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H4).
-------- assert (* Cut *) (euclidean__axioms.Col A B D) as H17.
--------- apply (@euclidean__tactics.not__nCol__Col A B D).
----------intro H17.
apply (@euclidean__tactics.Col__nCol__False A B D H17).
-----------apply (@lemma__collinear4.lemma__collinear4 E A B D H14 H15 H16).


--------- assert (* Cut *) (D = D) as H18.
---------- apply (@logic.eq__refl Point D).
---------- assert (* Cut *) (euclidean__axioms.Col C D D) as H19.
----------- right.
right.
left.
exact H18.
----------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H20.
------------ exists D.
split.
------------- exact H2.
------------- split.
-------------- exact H3.
-------------- split.
--------------- exact H17.
--------------- exact H19.
------------ apply (@H6 H20).
----- assert (* Cut *) (exists Q, (euclidean__axioms.BetS E Q A) /\ (euclidean__axioms.BetS D F Q)) as H14.
------ apply (@euclidean__axioms.postulate__Pasch__outer E D H F A H11 H12).
-------apply (@euclidean__tactics.nCol__notCol D A E H13).

------ destruct H14 as [Q H15].
destruct H15 as [H16 H17].
assert (* Cut *) (euclidean__axioms.Col E Q A) as H18.
------- right.
right.
right.
right.
left.
exact H16.
------- assert (* Cut *) (euclidean__axioms.Col D F Q) as H19.
-------- right.
right.
right.
right.
left.
exact H17.
-------- assert (* Cut *) (euclidean__axioms.Col E A Q) as H20.
--------- assert (* Cut *) ((euclidean__axioms.Col Q E A) /\ ((euclidean__axioms.Col Q A E) /\ ((euclidean__axioms.Col A E Q) /\ ((euclidean__axioms.Col E A Q) /\ (euclidean__axioms.Col A Q E))))) as H20.
---------- apply (@lemma__collinearorder.lemma__collinearorder E Q A H18).
---------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
--------- assert (* Cut *) (euclidean__axioms.Col E A B) as H21.
---------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H21.
----------- apply (@lemma__collinearorder.lemma__collinearorder A E B H0).
----------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H22.
---------- assert (* Cut *) (euclidean__axioms.neq E A) as H22.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H4).
----------- assert (* Cut *) (euclidean__axioms.Col A Q B) as H23.
------------ apply (@euclidean__tactics.not__nCol__Col A Q B).
-------------intro H23.
apply (@euclidean__tactics.Col__nCol__False A Q B H23).
--------------apply (@lemma__collinear4.lemma__collinear4 E A Q B H20 H21 H22).


------------ assert (* Cut *) (euclidean__axioms.Col A B Q) as H24.
------------- assert (* Cut *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col A B Q) /\ (euclidean__axioms.Col B Q A))))) as H24.
-------------- apply (@lemma__collinearorder.lemma__collinearorder A Q B H23).
-------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
------------- assert (* Cut *) (euclidean__axioms.Col F D Q) as H25.
-------------- assert (* Cut *) ((euclidean__axioms.Col F D Q) /\ ((euclidean__axioms.Col F Q D) /\ ((euclidean__axioms.Col Q D F) /\ ((euclidean__axioms.Col D Q F) /\ (euclidean__axioms.Col Q F D))))) as H25.
--------------- apply (@lemma__collinearorder.lemma__collinearorder D F Q H19).
--------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
-------------- assert (* Cut *) (euclidean__axioms.Col F D C) as H26.
--------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H26.
---------------- apply (@lemma__collinearorder.lemma__collinearorder C F D H1).
---------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H29.
--------------- assert (* Cut *) (euclidean__axioms.Col D Q C) as H27.
---------------- apply (@euclidean__tactics.not__nCol__Col D Q C).
-----------------intro H27.
apply (@euclidean__tactics.Col__nCol__False D Q C H27).
------------------apply (@lemma__collinear4.lemma__collinear4 F D Q C H25 H26 H5).


---------------- assert (* Cut *) (euclidean__axioms.Col C D Q) as H28.
----------------- assert (* Cut *) ((euclidean__axioms.Col Q D C) /\ ((euclidean__axioms.Col Q C D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D C Q) /\ (euclidean__axioms.Col C Q D))))) as H28.
------------------ apply (@lemma__collinearorder.lemma__collinearorder D Q C H27).
------------------ destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H33.
----------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H29.
------------------ exists Q.
split.
------------------- exact H2.
------------------- split.
-------------------- exact H3.
-------------------- split.
--------------------- exact H24.
--------------------- exact H28.
------------------ apply (@H6 H29).
--- assert (* Cut *) (~(euclidean__axioms.BetS F E H)) as H12.
---- intro H12.
assert (* Cut *) (~(euclidean__axioms.Col A D F)) as H13.
----- intro H13.
assert (* Cut *) (euclidean__axioms.Col F D C) as H14.
------ assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H14.
------- apply (@lemma__collinearorder.lemma__collinearorder C F D H1).
------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H17.
------ assert (* Cut *) (euclidean__axioms.Col F D A) as H15.
------- assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H15.
-------- apply (@lemma__collinearorder.lemma__collinearorder A D F H13).
-------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H23.
------- assert (* Cut *) (euclidean__axioms.Col D C A) as H16.
-------- apply (@euclidean__tactics.not__nCol__Col D C A).
---------intro H16.
apply (@euclidean__tactics.Col__nCol__False D C A H16).
----------apply (@lemma__collinear4.lemma__collinear4 F D C A H14 H15 H5).


-------- assert (* Cut *) (euclidean__axioms.Col C D A) as H17.
--------- assert (* Cut *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H17.
---------- apply (@lemma__collinearorder.lemma__collinearorder D C A H16).
---------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
--------- assert (* Cut *) (A = A) as H18.
---------- apply (@logic.eq__refl Point A).
---------- assert (* Cut *) (euclidean__axioms.Col A B A) as H19.
----------- right.
left.
exact H18.
----------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H20.
------------ exists A.
split.
------------- exact H2.
------------- split.
-------------- exact H3.
-------------- split.
--------------- exact H19.
--------------- exact H17.
------------ apply (@H6 H20).
----- assert (* Cut *) (exists R, (euclidean__axioms.BetS F R D) /\ (euclidean__axioms.BetS A E R)) as H14.
------ apply (@euclidean__axioms.postulate__Pasch__outer F A H E D H12 H7).
-------apply (@euclidean__tactics.nCol__notCol A D F H13).

------ destruct H14 as [R H15].
destruct H15 as [H16 H17].
assert (* Cut *) (euclidean__axioms.Col F R D) as H18.
------- right.
right.
right.
right.
left.
exact H16.
------- assert (* Cut *) (euclidean__axioms.Col A E R) as H19.
-------- right.
right.
right.
right.
left.
exact H17.
-------- assert (* Cut *) (euclidean__axioms.Col F D R) as H20.
--------- assert (* Cut *) ((euclidean__axioms.Col R F D) /\ ((euclidean__axioms.Col R D F) /\ ((euclidean__axioms.Col D F R) /\ ((euclidean__axioms.Col F D R) /\ (euclidean__axioms.Col D R F))))) as H20.
---------- apply (@lemma__collinearorder.lemma__collinearorder F R D H18).
---------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
--------- assert (* Cut *) (euclidean__axioms.Col F D C) as H21.
---------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H21.
----------- apply (@lemma__collinearorder.lemma__collinearorder C F D H1).
----------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H24.
---------- assert (* Cut *) (euclidean__axioms.Col D R C) as H22.
----------- apply (@euclidean__tactics.not__nCol__Col D R C).
------------intro H22.
apply (@euclidean__tactics.Col__nCol__False D R C H22).
-------------apply (@lemma__collinear4.lemma__collinear4 F D R C H20 H21 H5).


----------- assert (* Cut *) (euclidean__axioms.Col C D R) as H23.
------------ assert (* Cut *) ((euclidean__axioms.Col R D C) /\ ((euclidean__axioms.Col R C D) /\ ((euclidean__axioms.Col C D R) /\ ((euclidean__axioms.Col D C R) /\ (euclidean__axioms.Col C R D))))) as H23.
------------- apply (@lemma__collinearorder.lemma__collinearorder D R C H22).
------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H28.
------------ assert (* Cut *) (euclidean__axioms.Col E A R) as H24.
------------- assert (* Cut *) ((euclidean__axioms.Col E A R) /\ ((euclidean__axioms.Col E R A) /\ ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A))))) as H24.
-------------- apply (@lemma__collinearorder.lemma__collinearorder A E R H19).
-------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
------------- assert (* Cut *) (euclidean__axioms.Col E A B) as H25.
-------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H25.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A E B H0).
--------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
-------------- assert (* Cut *) (euclidean__axioms.neq A E) as H26.
--------------- assert (* Cut *) ((euclidean__axioms.neq E R) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A R))) as H26.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal A E R H17).
---------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H29.
--------------- assert (* Cut *) (euclidean__axioms.neq E A) as H27.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H26).
---------------- assert (* Cut *) (euclidean__axioms.Col A R B) as H28.
----------------- apply (@euclidean__tactics.not__nCol__Col A R B).
------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False A R B H28).
-------------------apply (@lemma__collinear4.lemma__collinear4 E A R B H24 H25 H27).


----------------- assert (* Cut *) (euclidean__axioms.Col A B R) as H29.
------------------ assert (* Cut *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.Col B R A))))) as H29.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A R B H28).
------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
------------------ assert (* Cut *) (euclidean__defs.Meet A B C D) as H30.
------------------- exists R.
split.
-------------------- exact H2.
-------------------- split.
--------------------- exact H3.
--------------------- split.
---------------------- exact H29.
---------------------- exact H23.
------------------- apply (@H6 H30).
---- assert (* Cut *) (~(E = F)) as H13.
----- intro H13.
assert (* Cut *) (euclidean__axioms.Col C D F) as H14.
------ assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H14.
------- apply (@lemma__collinearorder.lemma__collinearorder C F D H1).
------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H21.
------ assert (* Cut *) (euclidean__axioms.Col A B E) as H15.
------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H15.
-------- apply (@lemma__collinearorder.lemma__collinearorder A E B H0).
-------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H22.
------- assert (* Cut *) (euclidean__axioms.Col A B F) as H16.
-------- apply (@eq__ind__r euclidean__axioms.Point F (fun E0 => (euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__axioms.Col E0 F H) -> ((~(H = E0)) -> ((~(euclidean__axioms.BetS E0 F H)) -> ((~(euclidean__axioms.BetS F E0 H)) -> ((euclidean__axioms.Col A B E0) -> (euclidean__axioms.Col A B F))))))))) with (x := E).
---------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
exact H22.

--------- exact H13.
--------- exact H0.
--------- exact H4.
--------- exact H8.
--------- exact H9.
--------- exact H11.
--------- exact H12.
--------- exact H15.
-------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H17.
--------- exists F.
split.
---------- exact H2.
---------- split.
----------- exact H3.
----------- split.
------------ exact H16.
------------ exact H14.
--------- apply (@H6 H17).
----- assert ((E = F) \/ ((E = H) \/ ((F = H) \/ ((euclidean__axioms.BetS F E H) \/ ((euclidean__axioms.BetS E F H) \/ (euclidean__axioms.BetS E H F)))))) as H14 by exact H8.
assert (* Cut *) (euclidean__axioms.BetS E H F) as H15.
------ assert ((E = F) \/ ((E = H) \/ ((F = H) \/ ((euclidean__axioms.BetS F E H) \/ ((euclidean__axioms.BetS E F H) \/ (euclidean__axioms.BetS E H F)))))) as H15 by exact H14.
assert ((E = F) \/ ((E = H) \/ ((F = H) \/ ((euclidean__axioms.BetS F E H) \/ ((euclidean__axioms.BetS E F H) \/ (euclidean__axioms.BetS E H F)))))) as __TmpHyp by exact H15.
destruct __TmpHyp as [H16|H16].
------- assert (* Cut *) (~(~(euclidean__axioms.BetS E H F))) as H17.
-------- intro H17.
apply (@H13 H16).
-------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E H F)).
---------intro H18.
assert (* Cut *) (False) as H19.
---------- apply (@H13 H16).
---------- assert (* Cut *) (False) as H20.
----------- apply (@H17 H18).
----------- contradiction H20.

------- destruct H16 as [H17|H17].
-------- assert (* Cut *) (~(~(euclidean__axioms.BetS E H F))) as H18.
--------- intro H18.
assert (* Cut *) (euclidean__axioms.neq E H) as H19.
---------- apply (@eq__ind__r euclidean__axioms.Point H (fun E0 => (euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__axioms.Col E0 F H) -> ((~(H = E0)) -> ((~(euclidean__axioms.BetS E0 F H)) -> ((~(euclidean__axioms.BetS F E0 H)) -> ((~(E0 = F)) -> ((~(euclidean__axioms.BetS E0 H F)) -> (euclidean__axioms.neq E0 H)))))))))) with (x := E).
-----------intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
exact H22.

----------- exact H17.
----------- exact H0.
----------- exact H4.
----------- exact H8.
----------- exact H9.
----------- exact H11.
----------- exact H12.
----------- exact H13.
----------- exact H18.
---------- apply (@H19 H17).
--------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E H F)).
----------intro H19.
assert (* Cut *) (False) as H20.
----------- apply (@H18 H19).
----------- contradiction H20.

-------- destruct H17 as [H18|H18].
--------- assert (* Cut *) (~(~(euclidean__axioms.BetS E H F))) as H19.
---------- intro H19.
assert (* Cut *) (euclidean__axioms.neq F H) as H20.
----------- apply (@eq__ind__r euclidean__axioms.Point H (fun F0 => (euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.neq F0 D) -> ((euclidean__axioms.Col E F0 H) -> ((~(H = F0)) -> ((~(euclidean__axioms.BetS E F0 H)) -> ((~(euclidean__axioms.BetS F0 E H)) -> ((~(E = F0)) -> ((~(euclidean__axioms.BetS E H F0)) -> (euclidean__axioms.neq F0 H)))))))))) with (x := F).
------------intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
exact H23.

------------ exact H18.
------------ exact H1.
------------ exact H5.
------------ exact H8.
------------ exact H10.
------------ exact H11.
------------ exact H12.
------------ exact H13.
------------ exact H19.
----------- apply (@H20 H18).
---------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E H F)).
-----------intro H20.
assert (* Cut *) (False) as H21.
------------ apply (@H19 H20).
------------ contradiction H21.

--------- destruct H18 as [H19|H19].
---------- assert (* Cut *) (~(~(euclidean__axioms.BetS E H F))) as H20.
----------- intro H20.
apply (@H12 H19).
----------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E H F)).
------------intro H21.
assert (* Cut *) (False) as H22.
------------- apply (@H12 H19).
------------- assert (* Cut *) (False) as H23.
-------------- apply (@H20 H21).
-------------- contradiction H23.

---------- destruct H19 as [H20|H20].
----------- assert (* Cut *) (~(~(euclidean__axioms.BetS E H F))) as H21.
------------ intro H21.
apply (@H11 H20).
------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E H F)).
-------------intro H22.
assert (* Cut *) (False) as H23.
-------------- apply (@H11 H20).
-------------- assert (* Cut *) (False) as H24.
--------------- apply (@H21 H22).
--------------- contradiction H24.

----------- exact H20.
------ exact H15.
Qed.
