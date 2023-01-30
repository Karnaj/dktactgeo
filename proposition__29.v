Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__crossbar2.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplementinequality.
Require Export lemma__supplements.
Require Export lemma__supplementsymmetric.
Require Export logic.
Require Export proposition__15.
Require Export proposition__31.
Definition proposition__29 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS C H D) -> ((euclidean__axioms.BetS E G H) -> ((euclidean__axioms.TS A G H D) -> ((euclidean__defs.CongA A G H G H D) /\ ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (euclidean__axioms.Col C H D) as H5.
- right.
right.
right.
right.
left.
exact H2.
- assert (* Cut *) (euclidean__axioms.neq G H) as H6.
-- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E H))) as H6.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (H) H3).
--- assert (* AndElim *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E H))) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E H)) as H9.
----- exact H8.
----- destruct H9 as [H9 H10].
exact H7.
-- assert (* Cut *) (euclidean__axioms.neq A B) as H7.
--- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H7.
---- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
---- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H8.
----- exact H7.
----- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H10.
------ exact H9.
------ destruct H10 as [H10 H11].
exact H11.
--- assert (* Cut *) (euclidean__axioms.neq C D) as H8.
---- assert (* Cut *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H8.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (H) (D) H2).
----- assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D)) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
exact H12.
---- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS A R D) /\ ((euclidean__axioms.Col G H R) /\ (euclidean__axioms.nCol G H A))) as H9.
----- exact H4.
----- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS A R D) /\ ((euclidean__axioms.Col G H R) /\ (euclidean__axioms.nCol G H A)))) as H10.
------ exact H9.
------ destruct H10 as [R H10].
assert (* AndElim *) ((euclidean__axioms.BetS A R D) /\ ((euclidean__axioms.Col G H R) /\ (euclidean__axioms.nCol G H A))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col G H R) /\ (euclidean__axioms.nCol G H A)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.TS D G H A) as H15.
--------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (G) (H) (A) (D) H4).
--------- assert (* Cut *) (euclidean__axioms.nCol G H D) as H16.
---------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X A) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H D))) as H16.
----------- exact H15.
----------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X A) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H D))) as __TmpHyp.
------------ exact H16.
------------ assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS D X A) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H D)))) as H17.
------------- exact __TmpHyp.
------------- destruct H17 as [x H17].
assert (* AndElim *) ((euclidean__axioms.BetS D x A) /\ ((euclidean__axioms.Col G H x) /\ (euclidean__axioms.nCol G H D))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col G H x) /\ (euclidean__axioms.nCol G H D)) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X D) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H A))) as H22.
---------------- exact H4.
---------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X D) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H A))) as __TmpHyp0.
----------------- exact H22.
----------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A X D) /\ ((euclidean__axioms.Col G H X) /\ (euclidean__axioms.nCol G H A)))) as H23.
------------------ exact __TmpHyp0.
------------------ destruct H23 as [x0 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A x0 D) /\ ((euclidean__axioms.Col G H x0) /\ (euclidean__axioms.nCol G H A))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col G H x0) /\ (euclidean__axioms.nCol G H A)) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
exact H21.
---------- assert (* Cut *) (euclidean__axioms.nCol D H G) as H17.
----------- assert (* Cut *) ((euclidean__axioms.nCol H G D) /\ ((euclidean__axioms.nCol H D G) /\ ((euclidean__axioms.nCol D G H) /\ ((euclidean__axioms.nCol G D H) /\ (euclidean__axioms.nCol D H G))))) as H17.
------------ apply (@lemma__NCorder.lemma__NCorder (G) (H) (D) H16).
------------ assert (* AndElim *) ((euclidean__axioms.nCol H G D) /\ ((euclidean__axioms.nCol H D G) /\ ((euclidean__axioms.nCol D G H) /\ ((euclidean__axioms.nCol G D H) /\ (euclidean__axioms.nCol D H G))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol H D G) /\ ((euclidean__axioms.nCol D G H) /\ ((euclidean__axioms.nCol G D H) /\ (euclidean__axioms.nCol D H G)))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol D G H) /\ ((euclidean__axioms.nCol G D H) /\ (euclidean__axioms.nCol D H G))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol G D H) /\ (euclidean__axioms.nCol D H G)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
exact H25.
----------- assert (* Cut *) (euclidean__axioms.Col D H C) as H18.
------------ assert (* Cut *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C D H) /\ (euclidean__axioms.Col D H C))))) as H18.
------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (H) (D) H5).
------------- assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C D H) /\ (euclidean__axioms.Col D H C))))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C D H) /\ (euclidean__axioms.Col D H C)))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C D H) /\ (euclidean__axioms.Col D H C))) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col C D H) /\ (euclidean__axioms.Col D H C)) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
exact H26.
------------ assert (* Cut *) (H = H) as H19.
------------- apply (@logic.eq__refl (Point) H).
------------- assert (* Cut *) (euclidean__axioms.Col D H H) as H20.
-------------- right.
right.
left.
exact H19.
-------------- assert (* Cut *) (euclidean__axioms.neq C H) as H21.
--------------- assert (* Cut *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H21.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (H) (D) H2).
---------------- assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H24.
--------------- assert (* Cut *) (euclidean__axioms.nCol C H G) as H22.
---------------- apply (@euclidean__tactics.nCol__notCol (C) (H) (G)).
-----------------apply (@euclidean__tactics.nCol__not__Col (C) (H) (G)).
------------------apply (@lemma__NChelper.lemma__NChelper (D) (H) (G) (C) (H) (H17) (H18) (H20) H21).


---------------- assert (* Cut *) (C = C) as H23.
----------------- apply (@logic.eq__refl (Point) C).
----------------- assert (* Cut *) (euclidean__axioms.Col C H C) as H24.
------------------ right.
left.
exact H23.
------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H25.
------------------- assert (* Cut *) ((euclidean__axioms.neq R D) /\ ((euclidean__axioms.neq A R) /\ (euclidean__axioms.neq A D))) as H25.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (R) (D) H11).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq R D) /\ ((euclidean__axioms.neq A R) /\ (euclidean__axioms.neq A D))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ (euclidean__axioms.neq A D)) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
exact H8.
------------------- assert (* Cut *) (euclidean__axioms.nCol C D G) as H26.
-------------------- apply (@euclidean__tactics.nCol__notCol (C) (D) (G)).
---------------------apply (@euclidean__tactics.nCol__not__Col (C) (D) (G)).
----------------------apply (@lemma__NChelper.lemma__NChelper (C) (H) (G) (C) (D) (H22) (H24) (H5) H25).


-------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (S: euclidean__axioms.Point), (euclidean__axioms.BetS P G Q) /\ ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))))))))))) as H27.
--------------------- apply (@proposition__31.proposition__31 (G) (C) (D) (H) (H2) H26).
--------------------- assert (exists P: euclidean__axioms.Point, (exists (Q: euclidean__axioms.Point) (S: euclidean__axioms.Point), (euclidean__axioms.BetS P G Q) /\ ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))))))))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [P H28].
assert (exists Q: euclidean__axioms.Point, (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS P G Q) /\ ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))))))))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [Q H29].
assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS P G Q) /\ ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))))))))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [S H30].
assert (* AndElim *) ((euclidean__axioms.BetS P G Q) /\ ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))))))))))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.CongA Q G H G H C) /\ ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA Q G H C H G) /\ ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))))))))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA H G Q C H G) /\ ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))))) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.CongA P G H G H D) /\ ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))))))) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.CongA P G H D H G) /\ ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA H G P D H G) /\ ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))))) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Par P Q C D) /\ ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Cong P G H D) /\ ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))))) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong G Q C H) /\ ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))))) as H49.
---------------------------------- exact H48.
---------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Cong G S S H) /\ ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))))) as H51.
----------------------------------- exact H50.
----------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Cong P S S D) /\ ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))))) as H53.
------------------------------------ exact H52.
------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong C S S Q) /\ ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)))) as H55.
------------------------------------- exact H54.
------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.BetS P S D) /\ ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H))) as H57.
-------------------------------------- exact H56.
-------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.BetS C S Q) /\ (euclidean__axioms.BetS G S H)) as H59.
--------------------------------------- exact H58.
--------------------------------------- destruct H59 as [H59 H60].
assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H61.
---------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H61.
----------------------------------------- exact H45.
----------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------------------------------ exact H61.
------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H62.
------------------------------------------- exact __TmpHyp.
------------------------------------------- destruct H62 as [x H62].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H63.
-------------------------------------------- exact H62.
-------------------------------------------- destruct H63 as [x0 H63].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H64.
--------------------------------------------- exact H63.
--------------------------------------------- destruct H64 as [x1 H64].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H65.
---------------------------------------------- exact H64.
---------------------------------------------- destruct H65 as [x2 H65].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H66.
----------------------------------------------- exact H65.
----------------------------------------------- destruct H66 as [x3 H66].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H67.
------------------------------------------------ exact H66.
------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H69.
------------------------------------------------- exact H68.
------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col P Q x) /\ ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H71.
-------------------------------------------------- exact H70.
-------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col P Q x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H73.
--------------------------------------------------- exact H72.
--------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H75.
---------------------------------------------------- exact H74.
---------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H77.
----------------------------------------------------- exact H76.
----------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H79.
------------------------------------------------------ exact H78.
------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H81.
------------------------------------------------------- exact H80.
------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__defs.Meet P Q C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H83.
-------------------------------------------------------- exact H82.
-------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H85.
--------------------------------------------------------- exact H84.
--------------------------------------------------------- destruct H85 as [H85 H86].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H87.
---------------------------------------------------------- exact H0.
---------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
----------------------------------------------------------- exact H87.
----------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H88.
------------------------------------------------------------ exact __TmpHyp0.
------------------------------------------------------------ destruct H88 as [x4 H88].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H89.
------------------------------------------------------------- exact H88.
------------------------------------------------------------- destruct H89 as [x5 H89].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H90.
-------------------------------------------------------------- exact H89.
-------------------------------------------------------------- destruct H90 as [x6 H90].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H91.
--------------------------------------------------------------- exact H90.
--------------------------------------------------------------- destruct H91 as [x7 H91].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H92.
---------------------------------------------------------------- exact H91.
---------------------------------------------------------------- destruct H92 as [x8 H92].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H93.
----------------------------------------------------------------- exact H92.
----------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H95.
------------------------------------------------------------------ exact H94.
------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H97.
------------------------------------------------------------------- exact H96.
------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H99.
-------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H101.
--------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H103.
---------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H105.
----------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H107.
------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H109.
------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H111.
-------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H109.
---------------------------------------- assert (* Cut *) (P = P) as H62.
----------------------------------------- apply (@logic.eq__refl (Point) P).
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq P G) as H63.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G Q) /\ ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P Q))) as H63.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (G) (Q) H31).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G Q) /\ ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P Q))) as H64.
-------------------------------------------- exact H63.
-------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P Q)) as H66.
--------------------------------------------- exact H65.
--------------------------------------------- destruct H66 as [H66 H67].
exact H66.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G P) as H64.
------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (G) H63).
------------------------------------------- assert (* Cut *) (euclidean__defs.Out G P P) as H65.
-------------------------------------------- apply (@lemma__ray4.lemma__ray4 (G) (P) (P)).
---------------------------------------------right.
left.
exact H62.

--------------------------------------------- exact H64.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G S H) as H66.
--------------------------------------------- right.
right.
right.
right.
left.
exact H60.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H S) as H67.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col S H G) /\ ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col G H S) /\ (euclidean__axioms.Col H S G))))) as H67.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (S) (H) H66).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col S H G) /\ ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col G H S) /\ (euclidean__axioms.Col H S G))))) as H68.
------------------------------------------------ exact H67.
------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col S H G) /\ ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col G H S) /\ (euclidean__axioms.Col H S G)))) as H70.
------------------------------------------------- exact H69.
------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col G H S) /\ (euclidean__axioms.Col H S G))) as H72.
-------------------------------------------------- exact H71.
-------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col G H S) /\ (euclidean__axioms.Col H S G)) as H74.
--------------------------------------------------- exact H73.
--------------------------------------------------- destruct H74 as [H74 H75].
exact H74.
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H D P G H) as H68.
----------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (G) (H) (G) (H) (D) H39).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P G H) as H69.
------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (P) (G) (H)).
-------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (P) (G) (H)).
--------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (H) (D) (P) (G) (H) H68).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol G H P) as H70.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G P H) /\ ((euclidean__axioms.nCol G H P) /\ ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P H G) /\ (euclidean__axioms.nCol H G P))))) as H70.
-------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (P) (G) (H) H69).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G P H) /\ ((euclidean__axioms.nCol G H P) /\ ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P H G) /\ (euclidean__axioms.nCol H G P))))) as H71.
--------------------------------------------------- exact H70.
--------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol G H P) /\ ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P H G) /\ (euclidean__axioms.nCol H G P)))) as H73.
---------------------------------------------------- exact H72.
---------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P H G) /\ (euclidean__axioms.nCol H G P))) as H75.
----------------------------------------------------- exact H74.
----------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol P H G) /\ (euclidean__axioms.nCol H G P)) as H77.
------------------------------------------------------ exact H76.
------------------------------------------------------ destruct H77 as [H77 H78].
exact H73.
------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A P G H) as H71.
-------------------------------------------------- exists D.
exists R.
exists S.
split.
--------------------------------------------------- exact H13.
--------------------------------------------------- split.
---------------------------------------------------- exact H67.
---------------------------------------------------- split.
----------------------------------------------------- exact H11.
----------------------------------------------------- split.
------------------------------------------------------ exact H57.
------------------------------------------------------ split.
------------------------------------------------------- exact H14.
------------------------------------------------------- exact H70.
-------------------------------------------------- assert (* Cut *) (H = H) as H72.
--------------------------------------------------- exact H19.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H73.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq S H) /\ ((euclidean__axioms.neq G S) /\ (euclidean__axioms.neq G H))) as H73.
----------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (S) (H) H60).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq S H) /\ ((euclidean__axioms.neq G S) /\ (euclidean__axioms.neq G H))) as H74.
------------------------------------------------------ exact H73.
------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq G S) /\ (euclidean__axioms.neq G H)) as H76.
------------------------------------------------------- exact H75.
------------------------------------------------------- destruct H76 as [H76 H77].
exact H77.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G H H) as H74.
----------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (G) (H) (H)).
------------------------------------------------------right.
left.
exact H72.

------------------------------------------------------ exact H73.
----------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA H G A H G P)) as H75.
------------------------------------------------------ intro H75.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS P M H) /\ (euclidean__defs.Out G A M)) as H76.
------------------------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (A) (G) (H) (P) (H) (P) (H75) (H71) (H74) H65).
------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS P M H) /\ (euclidean__defs.Out G A M))) as H77.
-------------------------------------------------------- exact H76.
-------------------------------------------------------- destruct H77 as [M H77].
assert (* AndElim *) ((euclidean__axioms.BetS P M H) /\ (euclidean__defs.Out G A M)) as H78.
--------------------------------------------------------- exact H77.
--------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) (euclidean__axioms.Cong G S H S) as H80.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong S G H S) /\ ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S))) as H80.
----------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (S) (S) (H) H51).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong S G H S) /\ ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S))) as H81.
------------------------------------------------------------ exact H80.
------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S)) as H83.
------------------------------------------------------------- exact H82.
------------------------------------------------------------- destruct H83 as [H83 H84].
exact H84.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong S P S D) as H81.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong S P D S) /\ ((euclidean__axioms.Cong S P S D) /\ (euclidean__axioms.Cong P S D S))) as H81.
------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (P) (S) (S) (D) H53).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong S P D S) /\ ((euclidean__axioms.Cong S P S D) /\ (euclidean__axioms.Cong P S D S))) as H82.
------------------------------------------------------------- exact H81.
------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Cong S P S D) /\ (euclidean__axioms.Cong P S D S)) as H84.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- destruct H84 as [H84 H85].
exact H84.
----------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS D H K)) as H82.
------------------------------------------------------------ apply (@euclidean__axioms.postulate__Euclid5 (M) (G) (H) (P) (D) (S) (H57) (H60) (H78) (H80) (H81) H16).
------------------------------------------------------------ assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS D H K))) as H83.
------------------------------------------------------------- exact H82.
------------------------------------------------------------- destruct H83 as [K H83].
assert (* AndElim *) ((euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS D H K)) as H84.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* Cut *) (euclidean__axioms.Col G A M) as H86.
--------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (A) (M) H79).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G M K) as H87.
---------------------------------------------------------------- right.
right.
right.
right.
left.
exact H84.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G A) as H88.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G M) /\ ((euclidean__axioms.Col A M G) /\ ((euclidean__axioms.Col M G A) /\ ((euclidean__axioms.Col G M A) /\ (euclidean__axioms.Col M A G))))) as H88.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (M) H86).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A G M) /\ ((euclidean__axioms.Col A M G) /\ ((euclidean__axioms.Col M G A) /\ ((euclidean__axioms.Col G M A) /\ (euclidean__axioms.Col M A G))))) as H89.
------------------------------------------------------------------- exact H88.
------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A M G) /\ ((euclidean__axioms.Col M G A) /\ ((euclidean__axioms.Col G M A) /\ (euclidean__axioms.Col M A G)))) as H91.
-------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col M G A) /\ ((euclidean__axioms.Col G M A) /\ (euclidean__axioms.Col M A G))) as H93.
--------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col G M A) /\ (euclidean__axioms.Col M A G)) as H95.
---------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H93.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G K) as H89.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))))) as H89.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (M) (K) H87).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))))) as H90.
-------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G)))) as H92.
--------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))) as H94.
---------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G)) as H96.
----------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H90.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G M) as H90.
------------------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (G) (A) (M) H79).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M G) as H91.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (M) H90).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A K) as H92.
--------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (A) (K)).
----------------------------------------------------------------------intro H92.
apply (@euclidean__tactics.Col__nCol__False (G) (A) (K) (H92)).
-----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (G) (A) (K) (H88) (H89) H91).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G B) as H93.
---------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H1.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G K) as H94.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G K) /\ ((euclidean__axioms.Col A K G) /\ ((euclidean__axioms.Col K G A) /\ ((euclidean__axioms.Col G K A) /\ (euclidean__axioms.Col K A G))))) as H94.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (K) H92).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A G K) /\ ((euclidean__axioms.Col A K G) /\ ((euclidean__axioms.Col K G A) /\ ((euclidean__axioms.Col G K A) /\ (euclidean__axioms.Col K A G))))) as H95.
------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col A K G) /\ ((euclidean__axioms.Col K G A) /\ ((euclidean__axioms.Col G K A) /\ (euclidean__axioms.Col K A G)))) as H97.
-------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col K G A) /\ ((euclidean__axioms.Col G K A) /\ (euclidean__axioms.Col K A G))) as H99.
--------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col G K A) /\ (euclidean__axioms.Col K A G)) as H101.
---------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H95.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H95.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H95.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (B) H93).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H96.
-------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)))) as H98.
--------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))) as H100.
---------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)) as H102.
----------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H96.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G A K) as H96.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H96.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (B) H95).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H97.
--------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G)))) as H99.
---------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))) as H101.
----------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G)) as H103.
------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------ destruct H103 as [H103 H104].
exact H92.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A G) as H97.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H97.
--------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H98.
---------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H100.
----------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H100.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H98.
--------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H97).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B K) as H99.
---------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (K)).
-----------------------------------------------------------------------------intro H99.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (K) (H99)).
------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (A) (B) (K) (H95) (H96) H98).


---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H D K) as H100.
----------------------------------------------------------------------------- right.
right.
right.
left.
exact H85.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H D C) as H101.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H101.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (H) (C) H18).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H102.
-------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)))) as H104.
--------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))) as H106.
---------------------------------------------------------------------------------- exact H105.
---------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)) as H108.
----------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------- destruct H108 as [H108 H109].
exact H102.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H D) as H102.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H102.
-------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (H) (D) H2).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D))) as H103.
--------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq C H) /\ (euclidean__axioms.neq C D)) as H105.
---------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H103.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D K C) as H103.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (K) (C)).
---------------------------------------------------------------------------------intro H103.
apply (@euclidean__tactics.Col__nCol__False (D) (K) (C) (H103)).
----------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (D) (K) (C) (H100) (H101) H102).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D K) as H104.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K D C) /\ ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col C D K) /\ ((euclidean__axioms.Col D C K) /\ (euclidean__axioms.Col C K D))))) as H104.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (K) (C) H103).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K D C) /\ ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col C D K) /\ ((euclidean__axioms.Col D C K) /\ (euclidean__axioms.Col C K D))))) as H105.
----------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col C D K) /\ ((euclidean__axioms.Col D C K) /\ (euclidean__axioms.Col C K D)))) as H107.
------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col C D K) /\ ((euclidean__axioms.Col D C K) /\ (euclidean__axioms.Col C K D))) as H109.
------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col D C K) /\ (euclidean__axioms.Col C K D)) as H111.
-------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H109.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H105.
---------------------------------------------------------------------------------- exists K.
split.
----------------------------------------------------------------------------------- exact H7.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------- apply (@H61 H105).
------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.LtA H G P H G A)) as H76.
------------------------------------------------------- intro H76.
assert (* Cut *) (euclidean__axioms.nCol P G H) as H77.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H G P) /\ ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P G H) /\ ((euclidean__axioms.nCol G P H) /\ (euclidean__axioms.nCol P H G))))) as H77.
--------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (G) (H) (P) H70).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H G P) /\ ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P G H) /\ ((euclidean__axioms.nCol G P H) /\ (euclidean__axioms.nCol P H G))))) as H78.
---------------------------------------------------------- exact H77.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol H P G) /\ ((euclidean__axioms.nCol P G H) /\ ((euclidean__axioms.nCol G P H) /\ (euclidean__axioms.nCol P H G)))) as H80.
----------------------------------------------------------- exact H79.
----------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol P G H) /\ ((euclidean__axioms.nCol G P H) /\ (euclidean__axioms.nCol P H G))) as H82.
------------------------------------------------------------ exact H81.
------------------------------------------------------------ destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.nCol G P H) /\ (euclidean__axioms.nCol P H G)) as H84.
------------------------------------------------------------- exact H83.
------------------------------------------------------------- destruct H84 as [H84 H85].
exact H82.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA P G H H G P) as H78.
--------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (P) (G) (H) H77).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA P G H H G A) as H79.
---------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (H) (G) (P) (H) (G) (A) (P) (G) (H) (H76) H78).
---------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H G A)) as H80.
----------------------------------------------------------- intro H80.
assert (* Cut *) (euclidean__axioms.Col G H A) as H81.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))))) as H81.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (G) (A) H80).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))))) as H82.
-------------------------------------------------------------- exact H81.
-------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H)))) as H84.
--------------------------------------------------------------- exact H83.
--------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))) as H86.
---------------------------------------------------------------- exact H85.
---------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H)) as H88.
----------------------------------------------------------------- exact H87.
----------------------------------------------------------------- destruct H88 as [H88 H89].
exact H82.
------------------------------------------------------------ apply (@euclidean__tactics.Col__nCol__False (P) (G) (H) (H77)).
-------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (P) (G) (H)).
--------------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (A) (H14) H81).


----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A A G H) as H81.
------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H) (G) (A)).
-------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H) (G) (A) H80).

------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A G H H G A) as H82.
------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (H) (G) (A) (A) (G) (H) H81).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA P G H A G H) as H83.
-------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (P) (G) (H) (H) (G) (A) (A) (G) (H) (H79) H82).
-------------------------------------------------------------- assert (* Cut *) (H = H) as H84.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G H H) as H85.
---------------------------------------------------------------- exact H74.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp P G H H Q) as H86.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H85.
------------------------------------------------------------------ exact H31.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D H C) as H87.
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (H) (D) H2).
------------------------------------------------------------------ assert (* Cut *) (G = G) as H88.
------------------------------------------------------------------- apply (@logic.eq__refl (Point) G).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H G) as H89.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (H) H73).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H G G) as H90.
--------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (H) (G) (G)).
----------------------------------------------------------------------right.
left.
exact H88.

---------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp D H G G C) as H91.
---------------------------------------------------------------------- split.
----------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H D D H G) as H92.
----------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (G) (H) (D) H16).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA P G H D H G) as H93.
------------------------------------------------------------------------ exact H41.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G Q G H C) as H94.
------------------------------------------------------------------------- apply (@lemma__supplements.lemma__supplements (P) (G) (H) (H) (Q) (D) (H) (G) (G) (C) (H93) (H86) H91).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp A G H H B) as H95.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H G B H G Q) as H96.
--------------------------------------------------------------------------- apply (@lemma__supplementinequality.lemma__supplementinequality (A) (G) (H) (H) (B) (P) (G) (H) (H) (Q) (H95) (H86) H83).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B G A) as H97.
---------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (G) (B) H1).
---------------------------------------------------------------------------- assert (* Cut *) (G = G) as H98.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H G) as H99.
------------------------------------------------------------------------------ right.
left.
exact H98.
------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col G H B)) as H100.
------------------------------------------------------------------------------- intro H100.
assert (* Cut *) (euclidean__axioms.Col A G B) as H101.
-------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H1.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H102.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H102.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (B) H101).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H103.
----------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)))) as H105.
------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))) as H107.
------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)) as H109.
-------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
exact H110.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G H) as H103.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G B) /\ ((euclidean__axioms.Col H B G) /\ ((euclidean__axioms.Col B G H) /\ ((euclidean__axioms.Col G B H) /\ (euclidean__axioms.Col B H G))))) as H103.
----------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (B) H100).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H G B) /\ ((euclidean__axioms.Col H B G) /\ ((euclidean__axioms.Col B G H) /\ ((euclidean__axioms.Col G B H) /\ (euclidean__axioms.Col B H G))))) as H104.
------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col H B G) /\ ((euclidean__axioms.Col B G H) /\ ((euclidean__axioms.Col G B H) /\ (euclidean__axioms.Col B H G)))) as H106.
------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col B G H) /\ ((euclidean__axioms.Col G B H) /\ (euclidean__axioms.Col B H G))) as H108.
-------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col G B H) /\ (euclidean__axioms.Col B H G)) as H110.
--------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H108.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
exact H105.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H105.
------------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (B) H104).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G A H) as H106.
------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (A) (H)).
--------------------------------------------------------------------------------------intro H106.
apply (@euclidean__tactics.Col__nCol__False (G) (A) (H) (H106)).
---------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (G) (A) (H) (H102) (H103) H105).


------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H G A) as H107.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col G H A) /\ (euclidean__axioms.Col H A G))))) as H107.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (H) H106).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col G H A) /\ (euclidean__axioms.Col H A G))))) as H108.
---------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col G H A) /\ (euclidean__axioms.Col H A G)))) as H110.
----------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col G H A) /\ (euclidean__axioms.Col H A G))) as H112.
------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col G H A) /\ (euclidean__axioms.Col H A G)) as H114.
------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
exact H112.
-------------------------------------------------------------------------------------- apply (@H80 H107).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B G H A) as H101.
-------------------------------------------------------------------------------- exists G.
split.
--------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (G) (H) (B) H100).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A G H B) as H102.
--------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (G) (H) (B) (A) H101).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A P G H) as H103.
---------------------------------------------------------------------------------- exists D.
exists R.
exists S.
split.
----------------------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H11.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H14.
--------------------------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS P A G H) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS P A G H) /\ ((euclidean__defs.OS A P H G) /\ (euclidean__defs.OS P A H G))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (G) (H) (A) (P) H103).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.OS P A G H) /\ ((euclidean__defs.OS A P H G) /\ (euclidean__defs.OS P A H G))) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__defs.OS A P H G) /\ (euclidean__defs.OS P A H G)) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
exact H105.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS P G H B) as H105.
------------------------------------------------------------------------------------ apply (@lemma__planeseparation.lemma__planeseparation (G) (H) (P) (A) (B) (H104) H102).
------------------------------------------------------------------------------------ assert (* Cut *) (exists (L: euclidean__axioms.Point), (euclidean__axioms.BetS P L B) /\ ((euclidean__axioms.Col G H L) /\ (euclidean__axioms.nCol G H P))) as H106.
------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------- assert (exists L: euclidean__axioms.Point, ((euclidean__axioms.BetS P L B) /\ ((euclidean__axioms.Col G H L) /\ (euclidean__axioms.nCol G H P)))) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [L H107].
assert (* AndElim *) ((euclidean__axioms.BetS P L B) /\ ((euclidean__axioms.Col G H L) /\ (euclidean__axioms.nCol G H P))) as H108.
--------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col G H L) /\ (euclidean__axioms.nCol G H P)) as H110.
---------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* Cut *) (euclidean__axioms.BetS B L P) as H112.
----------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (L) (B) H108).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H C H G Q) as H113.
------------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (H) (G) (Q) (G) (H) (C) H94).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H G Q) as H114.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (H) (G) (Q)).
--------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (H) (G) (Q)).
---------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (H) (C) (H) (G) (Q) H113).


------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col G H Q)) as H115.
-------------------------------------------------------------------------------------------- intro H115.
assert (* Cut *) (euclidean__axioms.Col H G Q) as H116.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G Q) /\ ((euclidean__axioms.Col H Q G) /\ ((euclidean__axioms.Col Q G H) /\ ((euclidean__axioms.Col G Q H) /\ (euclidean__axioms.Col Q H G))))) as H116.
---------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (Q) H115).
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H G Q) /\ ((euclidean__axioms.Col H Q G) /\ ((euclidean__axioms.Col Q G H) /\ ((euclidean__axioms.Col G Q H) /\ (euclidean__axioms.Col Q H G))))) as H117.
----------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col H Q G) /\ ((euclidean__axioms.Col Q G H) /\ ((euclidean__axioms.Col G Q H) /\ (euclidean__axioms.Col Q H G)))) as H119.
------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col Q G H) /\ ((euclidean__axioms.Col G Q H) /\ (euclidean__axioms.Col Q H G))) as H121.
------------------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col G Q H) /\ (euclidean__axioms.Col Q H G)) as H123.
-------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
exact H117.
--------------------------------------------------------------------------------------------- apply (@H80).
----------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (H) (G) (A)).
-----------------------------------------------------------------------------------------------intro H117.
apply (@euclidean__tactics.Col__nCol__False (H) (G) (Q) (H114) H116).


-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS Q G P) as H116.
--------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (G) (Q) H31).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS B Q G H) as H117.
---------------------------------------------------------------------------------------------- exists P.
exists L.
exists G.
split.
----------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (G) (H) (B) H100).
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (G) (H) (Q) H115).
---------------------------------------------------------------------------------------------- assert (* Cut *) (Q = Q) as H118.
----------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) Q).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q G) as H119.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G P) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q P))) as H119.
------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (G) (P) H116).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G P) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q P))) as H120.
-------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q P)) as H122.
--------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
exact H122.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G Q) as H120.
------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (Q) (G) H119).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G Q Q) as H121.
-------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (G) (Q) (Q)).
---------------------------------------------------------------------------------------------------right.
left.
exact H118.

--------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS Q M H) /\ (euclidean__defs.Out G B M)) as H122.
--------------------------------------------------------------------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (B) (G) (H) (Q) (H) (Q) (H96) (H117) (H85) H121).
--------------------------------------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS Q M H) /\ (euclidean__defs.Out G B M))) as H123.
---------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------- destruct H123 as [M H123].
assert (* AndElim *) ((euclidean__axioms.BetS Q M H) /\ (euclidean__defs.Out G B M)) as H124.
----------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* Cut *) (euclidean__axioms.Cong G S H S) as H126.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong S G H S) /\ ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S))) as H126.
------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (S) (S) (H) H51).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong S G H S) /\ ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S))) as H127.
-------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Cong S G S H) /\ (euclidean__axioms.Cong G S H S)) as H129.
--------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H130.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS Q S C) as H127.
------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (S) (Q) H59).
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong S Q C S) as H128.
-------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (S) (C) (S) (Q) H55).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong S Q S C) as H129.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong Q S S C) /\ ((euclidean__axioms.Cong Q S C S) /\ (euclidean__axioms.Cong S Q S C))) as H129.
---------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (S) (Q) (C) (S) H128).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q S S C) /\ ((euclidean__axioms.Cong Q S C S) /\ (euclidean__axioms.Cong S Q S C))) as H130.
----------------------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Cong Q S C S) /\ (euclidean__axioms.Cong S Q S C)) as H132.
------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
exact H133.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H C) as H130.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H C G) /\ ((euclidean__axioms.nCol H G C) /\ ((euclidean__axioms.nCol G C H) /\ ((euclidean__axioms.nCol C G H) /\ (euclidean__axioms.nCol G H C))))) as H130.
----------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (H) (G) H22).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H C G) /\ ((euclidean__axioms.nCol H G C) /\ ((euclidean__axioms.nCol G C H) /\ ((euclidean__axioms.nCol C G H) /\ (euclidean__axioms.nCol G H C))))) as H131.
------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.nCol H G C) /\ ((euclidean__axioms.nCol G C H) /\ ((euclidean__axioms.nCol C G H) /\ (euclidean__axioms.nCol G H C)))) as H133.
------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.nCol G C H) /\ ((euclidean__axioms.nCol C G H) /\ (euclidean__axioms.nCol G H C))) as H135.
-------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.nCol C G H) /\ (euclidean__axioms.nCol G H C)) as H137.
--------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H138.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS C H K)) as H131.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Euclid5 (M) (G) (H) (Q) (C) (S) (H127) (H60) (H124) (H126) (H129) H130).
----------------------------------------------------------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS C H K))) as H132.
------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------ destruct H132 as [K H132].
assert (* AndElim *) ((euclidean__axioms.BetS G M K) /\ (euclidean__axioms.BetS C H K)) as H133.
------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* Cut *) (euclidean__axioms.Col G B M) as H135.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (B) (M) H125).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G M K) as H136.
--------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H133.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G B) as H137.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G M) /\ ((euclidean__axioms.Col B M G) /\ ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G))))) as H137.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (B) (M) H135).
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B G M) /\ ((euclidean__axioms.Col B M G) /\ ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G))))) as H138.
------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col B M G) /\ ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G)))) as H140.
------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G))) as H142.
-------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G)) as H144.
--------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
exact H142.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G K) as H138.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))))) as H138.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (M) (K) H136).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))))) as H139.
------------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G)))) as H141.
-------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G))) as H143.
--------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col G K M) /\ (euclidean__axioms.Col K M G)) as H145.
---------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
exact H139.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G M) as H139.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__raystrict.lemma__raystrict (G) (B) (M) H125).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq M G) as H140.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (M) H139).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B K) as H141.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (B) (K)).
---------------------------------------------------------------------------------------------------------------------intro H141.
apply (@euclidean__tactics.Col__nCol__False (G) (B) (K) (H141)).
----------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (G) (B) (K) (H137) (H138) H140).


-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H142.
--------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H97.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G K) as H143.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G K) /\ ((euclidean__axioms.Col B K G) /\ ((euclidean__axioms.Col K G B) /\ ((euclidean__axioms.Col G K B) /\ (euclidean__axioms.Col K B G))))) as H143.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (B) (K) H141).
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B G K) /\ ((euclidean__axioms.Col B K G) /\ ((euclidean__axioms.Col K G B) /\ ((euclidean__axioms.Col G K B) /\ (euclidean__axioms.Col K B G))))) as H144.
------------------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Col B K G) /\ ((euclidean__axioms.Col K G B) /\ ((euclidean__axioms.Col G K B) /\ (euclidean__axioms.Col K B G)))) as H146.
------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Col K G B) /\ ((euclidean__axioms.Col G K B) /\ (euclidean__axioms.Col K B G))) as H148.
-------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col G K B) /\ (euclidean__axioms.Col K B G)) as H150.
--------------------------------------------------------------------------------------------------------------------------- exact H149.
--------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
exact H144.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H144.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H144.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (A) H142).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H145.
------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B)))) as H147.
-------------------------------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))) as H149.
--------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B)) as H151.
---------------------------------------------------------------------------------------------------------------------------- exact H150.
---------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
exact H145.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B K) as H145.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H145.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (B) (A) H144).
------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H146.
-------------------------------------------------------------------------------------------------------------------------- exact H145.
-------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)))) as H148.
--------------------------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))) as H150.
---------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G)) as H152.
----------------------------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
exact H141.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B G) as H146.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A))) as H146.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (G) (A) H97).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A))) as H147.
--------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A)) as H149.
---------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
exact H149.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H147.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (G) H146).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A K) as H148.
--------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (K)).
----------------------------------------------------------------------------------------------------------------------------intro H148.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (K) (H148)).
-----------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (B) (A) (K) (H144) (H145) H147).


--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B K) as H149.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B K) /\ ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))))) as H149.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (K) H148).
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B K) /\ ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))))) as H150.
------------------------------------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------------------------------------ destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B)))) as H152.
------------------------------------------------------------------------------------------------------------------------------- exact H151.
------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))) as H154.
-------------------------------------------------------------------------------------------------------------------------------- exact H153.
-------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B)) as H156.
--------------------------------------------------------------------------------------------------------------------------------- exact H155.
--------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
exact H150.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H C K) as H150.
----------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
left.
exact H134.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H C D) as H151.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H151.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (H) (C) H18).
------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H152.
-------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)))) as H154.
--------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))) as H156.
---------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)) as H158.
----------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
exact H154.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H C) as H152.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H C) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C))) as H152.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (H) (C) H87).
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H C) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C))) as H153.
--------------------------------------------------------------------------------------------------------------------------------- exact H152.
--------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C)) as H155.
---------------------------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
exact H153.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C K D) as H153.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (K) (D)).
---------------------------------------------------------------------------------------------------------------------------------intro H153.
apply (@euclidean__tactics.Col__nCol__False (C) (K) (D) (H153)).
----------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (C) (K) (D) (H150) (H151) H152).


-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D K) as H154.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col K D C) /\ ((euclidean__axioms.Col D C K) /\ ((euclidean__axioms.Col C D K) /\ (euclidean__axioms.Col D K C))))) as H154.
---------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (K) (D) H153).
---------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col K D C) /\ ((euclidean__axioms.Col D C K) /\ ((euclidean__axioms.Col C D K) /\ (euclidean__axioms.Col D K C))))) as H155.
----------------------------------------------------------------------------------------------------------------------------------- exact H154.
----------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Col K D C) /\ ((euclidean__axioms.Col D C K) /\ ((euclidean__axioms.Col C D K) /\ (euclidean__axioms.Col D K C)))) as H157.
------------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col D C K) /\ ((euclidean__axioms.Col C D K) /\ (euclidean__axioms.Col D K C))) as H159.
------------------------------------------------------------------------------------------------------------------------------------- exact H158.
------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col C D K) /\ (euclidean__axioms.Col D K C)) as H161.
-------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
exact H161.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H155.
---------------------------------------------------------------------------------------------------------------------------------- exists K.
split.
----------------------------------------------------------------------------------------------------------------------------------- exact H7.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------------------------- apply (@H61 H155).
------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H G P)) as H77.
-------------------------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col G H P) as H78.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G H P) /\ ((euclidean__axioms.Col G P H) /\ ((euclidean__axioms.Col P H G) /\ ((euclidean__axioms.Col H P G) /\ (euclidean__axioms.Col P G H))))) as H78.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (G) (P) H77).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G H P) /\ ((euclidean__axioms.Col G P H) /\ ((euclidean__axioms.Col P H G) /\ ((euclidean__axioms.Col H P G) /\ (euclidean__axioms.Col P G H))))) as H79.
----------------------------------------------------------- exact H78.
----------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col G P H) /\ ((euclidean__axioms.Col P H G) /\ ((euclidean__axioms.Col H P G) /\ (euclidean__axioms.Col P G H)))) as H81.
------------------------------------------------------------ exact H80.
------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col P H G) /\ ((euclidean__axioms.Col H P G) /\ (euclidean__axioms.Col P G H))) as H83.
------------------------------------------------------------- exact H82.
------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col H P G) /\ (euclidean__axioms.Col P G H)) as H85.
-------------------------------------------------------------- exact H84.
-------------------------------------------------------------- destruct H85 as [H85 H86].
exact H79.
--------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (G) (H) (P) (H70) H78).
-------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H G A)) as H78.
--------------------------------------------------------- intro H78.
assert (* Cut *) (euclidean__axioms.Col G H A) as H79.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))))) as H79.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (G) (A) H78).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))))) as H80.
------------------------------------------------------------ exact H79.
------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H)))) as H82.
------------------------------------------------------------- exact H81.
------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col A H G) /\ ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H))) as H84.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col H A G) /\ (euclidean__axioms.Col A G H)) as H86.
--------------------------------------------------------------- exact H85.
--------------------------------------------------------------- destruct H86 as [H86 H87].
exact H80.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H A) as H80.
----------------------------------------------------------- exact H14.
----------------------------------------------------------- apply (@H77).
------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (H) (G) (P)).
-------------------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (A) (H80) H79).


--------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA H G A H G P))) as H79.
---------------------------------------------------------- intro H79.
assert (* Cut *) (euclidean__defs.LtA H G A H G P) as H80.
----------------------------------------------------------- apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 (H) (G) (A) (H) (G) (P)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H) (G) (A) H78).

------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H) (G) (P) H77).

------------------------------------------------------------ exact H79.
------------------------------------------------------------ exact H76.
----------------------------------------------------------- apply (@H75 H80).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G P P G H) as H80.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H80.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H) (G) (P)).
-------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H) (G) (P) H77).

----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G P G H D) as H81.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H81.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H) (G) (P) (P) (G) (H) (G) (H) (D) (H80) H39).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA G H D D H G) as H82.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H82.
-------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
-------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (G) (H) (D) H16).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G P D H G) as H83.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H83.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
--------------------------------------------------------------- exact H43.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A D H G) as H84.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H84.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
---------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H) (G) (A) (H) (G) (P) (D) (H) (G) (H84) H83).
--------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A G H)) as H85.
---------------------------------------------------------------- intro H85.
assert (* Cut *) (euclidean__axioms.Col G H A) as H86.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A H G) /\ (euclidean__axioms.Col H G A))))) as H86.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (H) H85).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G A H) /\ ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A H G) /\ (euclidean__axioms.Col H G A))))) as H87.
------------------------------------------------------------------- exact H86.
------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col G H A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A H G) /\ (euclidean__axioms.Col H G A)))) as H89.
-------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A H G) /\ (euclidean__axioms.Col H G A))) as H91.
--------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col A H G) /\ (euclidean__axioms.Col H G A)) as H93.
---------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------- destruct H93 as [H93 H94].
exact H89.
----------------------------------------------------------------- apply (@H77).
------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (H) (G) (P)).
-------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (A) (H14) H86).


---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G H H G A) as H86.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H86.
------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (G) (H)).
-------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (G) (H) H85).

----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G H D H G) as H87.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H87.
------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (G) (H) (H) (G) (A) (D) (H) (G) (H86) H84).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol D H G) as H88.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H88.
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
-------------------------------------------------------------------- exact H17.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D H G G H D) as H89.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H89.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
--------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (D) (H) (G) H88).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G H G H D) as H90.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H90.
---------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
---------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (G) (H) (D) (H) (G) (G) (H) (D) (H87) H89).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H G E) as H91.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H91.
----------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (G) (H) H3).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G H E G B) as H92.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H92.
------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------------ apply (@proposition__15.proposition__15a (A) (B) (H) (E) (G) (H1) (H91)).
-------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (G) (H) H85).

----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G B A G H) as H93.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H93.
------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (G) (H) (E) (G) (B) H92).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E G B G H D) as H94.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H94.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
-------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (E) (G) (B) (A) (G) (H) (G) (H) (D) (H93) H90).
------------------------------------------------------------------------- assert (* Cut *) (H = H) as H95.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H95.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
--------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G H H) as H96.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H96.
---------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
---------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp A G H H B) as H97.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H97.
----------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------ exact H1.
---------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B G H)) as H98.
----------------------------------------------------------------------------- intro H98.
assert (* Cut *) (euclidean__axioms.Col A G B) as H99.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H99.
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H1.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B G A) as H100.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H100.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (B) H99).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H101.
--------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)))) as H103.
---------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))) as H105.
----------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)) as H107.
------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
exact H108.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H101.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H101.
--------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H102.
---------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H104.
----------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H102.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H102.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H102.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
---------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (B) H101).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H A) as H103.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H103.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
----------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (H) (A)).
------------------------------------------------------------------------------------intro H104.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (A) (H104)).
-------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (G) (H) (A) (H98) (H100) H102).


---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G H) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (A) H103).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G)))) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))) as H109.
--------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G)) as H111.
---------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H109.
----------------------------------------------------------------------------------- apply (@H77).
------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (H) (G) (P)).
-------------------------------------------------------------------------------------intro H105.
apply (@H85 H104).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B G H B G H) as H99.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H99.
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (B) (G) (H)).
--------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (G) (H) H98).

------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA G H D A G H) as H100.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H100.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
-------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (G) (H) (G) (H) (D) H90).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G H H G A) as H101.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H101.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
--------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H D H G A) as H102.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H102.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
---------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (H) (D) (A) (G) (H) (H) (G) (A) (H100) H101).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp B G H H A) as H103.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H103.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
----------------------------------------------------------------------------------- apply (@lemma__supplementsymmetric.lemma__supplementsymmetric (A) (G) (H) (B) (H) H97).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RT B G H G H D) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G P) as H104.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA H G A H G P) H79).
------------------------------------------------------------------------------------ exists B.
exists G.
exists A.
exists H.
exists H.
split.
------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------- exact H104.
Qed.
