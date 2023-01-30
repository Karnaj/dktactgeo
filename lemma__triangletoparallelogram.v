Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__Playfair.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__31.
Require Export proposition__33.
Definition lemma__triangletoparallelogram : forall (A: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Par D C E F) -> ((euclidean__axioms.Col E F A) -> (exists (X: euclidean__axioms.Point), (euclidean__defs.PG A X C D) /\ (euclidean__axioms.Col E F X))).
Proof.
intro A.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.nCol D C E) as H1.
- assert (* Cut *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)))) as H1.
-- apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (E) (F) H).
-- assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F))) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
exact H2.
- assert (* Cut *) (euclidean__axioms.neq D C) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D)))))) as H2.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (C) (E) H1).
--- assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D)))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E D)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H3.
-- assert (* Cut *) (euclidean__axioms.neq C D) as H3.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (C) H2).
--- assert (* Cut *) (exists (B: euclidean__axioms.Point), (euclidean__axioms.BetS C D B) /\ (euclidean__axioms.Cong D B C D)) as H4.
---- apply (@lemma__extension.lemma__extension (C) (D) (C) (D) (H3) H3).
---- assert (exists B: euclidean__axioms.Point, ((euclidean__axioms.BetS C D B) /\ (euclidean__axioms.Cong D B C D))) as H5.
----- exact H4.
----- destruct H5 as [B H5].
assert (* AndElim *) ((euclidean__axioms.BetS C D B) /\ (euclidean__axioms.Cong D B C D)) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.BetS B D C) as H8.
------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (D) (B) H6).
------- assert (* Cut *) (euclidean__axioms.nCol C E F) as H9.
-------- assert (* Cut *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)))) as H9.
--------- apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (E) (F) H).
--------- assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.nCol D E F) /\ ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol C E F) /\ (euclidean__axioms.nCol D C F)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
exact H14.
-------- assert (* Cut *) (euclidean__axioms.neq E F) as H10.
--------- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))))) as H10.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (E) (F) H9).
---------- assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
exact H13.
--------- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H11.
---------- intro H11.
assert (* Cut *) (euclidean__axioms.Col C D B) as H12.
----------- right.
right.
right.
right.
left.
exact H6.
----------- assert (* Cut *) (euclidean__axioms.Col B C D) as H13.
------------ assert (* Cut *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H13.
------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (B) H12).
------------- assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
exact H18.
------------ assert (* Cut *) (euclidean__axioms.neq B C) as H14.
------------- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C))) as H14.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (D) (C) H8).
-------------- assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C)) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
exact H18.
------------- assert (* Cut *) (euclidean__axioms.Col C A D) as H15.
-------------- apply (@euclidean__tactics.not__nCol__Col (C) (A) (D)).
---------------intro H15.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (D) (H15)).
----------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (A) (D) (H11) (H13) H14).


-------------- assert (* Cut *) (euclidean__axioms.Col D C A) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))))) as H16.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (D) H15).
---------------- assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C)))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ (euclidean__axioms.Col D A C)) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
exact H21.
--------------- assert (* Cut *) (euclidean__defs.Meet D C E F) as H17.
---------------- exists A.
split.
----------------- exact H2.
----------------- split.
------------------ exact H10.
------------------ split.
------------------- exact H16.
------------------- exact H0.
---------------- assert (* Cut *) (~(euclidean__defs.Meet D C E F)) as H18.
----------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H18.
------------------ exact H.
------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------- exact H18.
------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H19.
-------------------- exact __TmpHyp.
-------------------- destruct H19 as [x H19].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H20.
--------------------- exact H19.
--------------------- destruct H20 as [x0 H20].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H21.
---------------------- exact H20.
---------------------- destruct H21 as [x1 H21].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H22.
----------------------- exact H21.
----------------------- destruct H22 as [x2 H22].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H23.
------------------------ exact H22.
------------------------ destruct H23 as [x3 H23].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H24.
------------------------- exact H23.
------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H26.
-------------------------- exact H25.
-------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col E F x1) /\ ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col E F x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((~(euclidean__defs.Meet D C E F)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
exact H40.
----------------- apply (@H18 H17).
---------- assert (* Cut *) (exists (c: euclidean__axioms.Point) (b: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS c A b) /\ ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))))))))))) as H12.
----------- apply (@proposition__31.proposition__31 (A) (B) (C) (D) (H8)).
------------apply (@euclidean__tactics.nCol__notCol (B) (C) (A) H11).

----------- assert (exists c: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS c A b) /\ ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))))))))) as H13.
------------ exact H12.
------------ destruct H13 as [c H13].
assert (exists b: euclidean__axioms.Point, (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS c A b) /\ ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))))))))) as H14.
------------- exact H13.
------------- destruct H14 as [b H14].
assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS c A b) /\ ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))))))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [M H15].
assert (* AndElim *) ((euclidean__axioms.BetS c A b) /\ ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))))))))))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.CongA b A D A D B) /\ ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))))))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.CongA b A D B D A) /\ ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))))))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.CongA D A b B D A) /\ ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.CongA c A D A D C) /\ ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))))))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.CongA c A D C D A) /\ ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.CongA D A c C D A) /\ ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par c b B C) /\ ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong c A D C) /\ ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))))) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Cong A b B D) /\ ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))))) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Cong A M M D) /\ ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))))) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Cong c M M C) /\ ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))))) as H38.
-------------------------- exact H37.
-------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong B M M b) /\ ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)))) as H40.
--------------------------- exact H39.
--------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.BetS c M C) /\ ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D))) as H42.
---------------------------- exact H41.
---------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.BetS B M b) /\ (euclidean__axioms.BetS A M D)) as H44.
----------------------------- exact H43.
----------------------------- destruct H44 as [H44 H45].
assert (* Cut *) (euclidean__axioms.BetS b M B) as H46.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (b) H44).
------------------------------ assert (* Cut *) (euclidean__axioms.nCol b B C) as H47.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol c b B) /\ ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)))) as H47.
-------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (c) (b) (B) (C) H30).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol c b B) /\ ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)))) as H48.
--------------------------------- exact H47.
--------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C))) as H50.
---------------------------------- exact H49.
---------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)) as H52.
----------------------------------- exact H51.
----------------------------------- destruct H52 as [H52 H53].
exact H52.
------------------------------- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS b R D) /\ (euclidean__axioms.BetS C R M)) as H48.
-------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (b) (C) (B) (M) (D) (H46) (H6) H47).
-------------------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS b R D) /\ (euclidean__axioms.BetS C R M))) as H49.
--------------------------------- exact H48.
--------------------------------- destruct H49 as [R H49].
assert (* AndElim *) ((euclidean__axioms.BetS b R D) /\ (euclidean__axioms.BetS C R M)) as H50.
---------------------------------- exact H49.
---------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) (euclidean__axioms.BetS C M c) as H52.
----------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (M) (C) H42).
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS C R c) as H53.
------------------------------------ apply (@lemma__3__6b.lemma__3__6b (C) (R) (M) (c) (H51) H52).
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS b A c) as H54.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (A) (b) H16).
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol c b C) as H55.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol c b B) /\ ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)))) as H55.
--------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (c) (b) (B) (C) H30).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol c b B) /\ ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)))) as H56.
---------------------------------------- exact H55.
---------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol c B C) /\ ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C))) as H58.
----------------------------------------- exact H57.
----------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol b B C) /\ (euclidean__axioms.nCol c b C)) as H60.
------------------------------------------ exact H59.
------------------------------------------ destruct H60 as [H60 H61].
exact H61.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol b c C) as H56.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol b c C) /\ ((euclidean__axioms.nCol b C c) /\ ((euclidean__axioms.nCol C c b) /\ ((euclidean__axioms.nCol c C b) /\ (euclidean__axioms.nCol C b c))))) as H56.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder (c) (b) (C) H55).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol b c C) /\ ((euclidean__axioms.nCol b C c) /\ ((euclidean__axioms.nCol C c b) /\ ((euclidean__axioms.nCol c C b) /\ (euclidean__axioms.nCol C b c))))) as H57.
----------------------------------------- exact H56.
----------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol b C c) /\ ((euclidean__axioms.nCol C c b) /\ ((euclidean__axioms.nCol c C b) /\ (euclidean__axioms.nCol C b c)))) as H59.
------------------------------------------ exact H58.
------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol C c b) /\ ((euclidean__axioms.nCol c C b) /\ (euclidean__axioms.nCol C b c))) as H61.
------------------------------------------- exact H60.
------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol c C b) /\ (euclidean__axioms.nCol C b c)) as H63.
-------------------------------------------- exact H62.
-------------------------------------------- destruct H63 as [H63 H64].
exact H57.
--------------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS b Q R) /\ (euclidean__axioms.BetS C Q A)) as H57.
---------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (b) (C) (c) (A) (R) (H54) (H53) H56).
---------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS b Q R) /\ (euclidean__axioms.BetS C Q A))) as H58.
----------------------------------------- exact H57.
----------------------------------------- destruct H58 as [Q H58].
assert (* AndElim *) ((euclidean__axioms.BetS b Q R) /\ (euclidean__axioms.BetS C Q A)) as H59.
------------------------------------------ exact H58.
------------------------------------------ destruct H59 as [H59 H60].
assert (* Cut *) (euclidean__axioms.BetS b Q D) as H61.
------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (b) (Q) (R) (D) (H59) H50).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D B) as H62.
-------------------------------------------- right.
right.
right.
right.
left.
exact H6.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H63.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H63.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (B) H62).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H64.
----------------------------------------------- exact H63.
----------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)))) as H66.
------------------------------------------------ exact H65.
------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))) as H68.
------------------------------------------------- exact H67.
------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C)) as H70.
-------------------------------------------------- exact H69.
-------------------------------------------------- destruct H70 as [H70 H71].
exact H68.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Par c b D C) as H64.
---------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (c) (b) (D) (B) (C) (H30) (H63) H2).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Par D C c b) as H65.
----------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (c) (b) (D) (C) H64).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c A b) as H66.
------------------------------------------------ right.
right.
right.
right.
left.
exact H16.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col c b A) as H67.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A c b) /\ ((euclidean__axioms.Col A b c) /\ ((euclidean__axioms.Col b c A) /\ ((euclidean__axioms.Col c b A) /\ (euclidean__axioms.Col b A c))))) as H67.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (c) (A) (b) H66).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A c b) /\ ((euclidean__axioms.Col A b c) /\ ((euclidean__axioms.Col b c A) /\ ((euclidean__axioms.Col c b A) /\ (euclidean__axioms.Col b A c))))) as H68.
--------------------------------------------------- exact H67.
--------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col A b c) /\ ((euclidean__axioms.Col b c A) /\ ((euclidean__axioms.Col c b A) /\ (euclidean__axioms.Col b A c)))) as H70.
---------------------------------------------------- exact H69.
---------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col b c A) /\ ((euclidean__axioms.Col c b A) /\ (euclidean__axioms.Col b A c))) as H72.
----------------------------------------------------- exact H71.
----------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col c b A) /\ (euclidean__axioms.Col b A c)) as H74.
------------------------------------------------------ exact H73.
------------------------------------------------------ destruct H74 as [H74 H75].
exact H74.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A b) as H68.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A b) /\ ((euclidean__axioms.neq c A) /\ (euclidean__axioms.neq c b))) as H68.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (c) (A) (b) H16).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A b) /\ ((euclidean__axioms.neq c A) /\ (euclidean__axioms.neq c b))) as H69.
---------------------------------------------------- exact H68.
---------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq c A) /\ (euclidean__axioms.neq c b)) as H71.
----------------------------------------------------- exact H70.
----------------------------------------------------- destruct H71 as [H71 H72].
exact H69.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D C A b) as H69.
--------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (D) (C) (A) (c) (b) (H65) (H67) H68).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b D C) as H70.
---------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (D) (C) (A) (b) H69).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Par b A C D) as H71.
----------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par b A D C) /\ ((euclidean__defs.Par A b C D) /\ (euclidean__defs.Par b A C D))) as H71.
------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (A) (b) (D) (C) H70).
------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par b A D C) /\ ((euclidean__defs.Par A b C D) /\ (euclidean__defs.Par b A C D))) as H72.
------------------------------------------------------- exact H71.
------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.Par A b C D) /\ (euclidean__defs.Par b A C D)) as H74.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- destruct H74 as [H74 H75].
exact H75.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D D B) as H72.
------------------------------------------------------ apply (@euclidean__axioms.cn__equalityreverse (B) D).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A b D B) as H73.
------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (b) (B) (D) (D) (B) (H34) H72).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A b C D) as H74.
-------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (b) (D) (B) (C) (D) (H73) H7).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b A C D) as H75.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong b A D C) /\ ((euclidean__axioms.Cong b A C D) /\ (euclidean__axioms.Cong A b D C))) as H75.
---------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (b) (C) (D) H74).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong b A D C) /\ ((euclidean__axioms.Cong b A C D) /\ (euclidean__axioms.Cong A b D C))) as H76.
----------------------------------------------------------- exact H75.
----------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Cong b A C D) /\ (euclidean__axioms.Cong A b D C)) as H78.
------------------------------------------------------------ exact H77.
------------------------------------------------------------ destruct H78 as [H78 H79].
exact H78.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A Q C) as H76.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (Q) (A) H60).
---------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H77.
----------------------------------------------------------- apply (@proposition__33.proposition__33 (b) (A) (C) (D) (Q) (H71) (H75) (H61) H76).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C D) as H78.
------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H78.
------------------------------------------------------------- exact H77.
------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) ((euclidean__defs.Par A b C D) /\ ((euclidean__defs.Par b A D C) /\ (euclidean__defs.Par A b D C))) as H80.
-------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (b) (A) (C) (D) H71).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par A b C D) /\ ((euclidean__defs.Par b A D C) /\ (euclidean__defs.Par A b D C))) as H81.
--------------------------------------------------------------- exact H80.
--------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__defs.Par b A D C) /\ (euclidean__defs.Par A b D C)) as H83.
---------------------------------------------------------------- exact H82.
---------------------------------------------------------------- destruct H83 as [H83 H84].
exact H81.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A D b C) as H79.
------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H79.
-------------------------------------------------------------- exact H77.
-------------------------------------------------------------- destruct H79 as [H79 H80].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (b) (C) (A) (D) H79).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A b C D) as H80.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H78.
--------------------------------------------------------------- exact H79.
-------------------------------------------------------------- assert (* Cut *) (E = E) as H81.
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H81.
---------------------------------------------------------------- exact H77.
---------------------------------------------------------------- destruct H81 as [H81 H82].
apply (@logic.eq__refl (Point) E).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F E) as H82.
---------------------------------------------------------------- right.
left.
exact H81.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F b) as H83.
----------------------------------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H83.
------------------------------------------------------------------ apply (@euclidean__tactics.eq__or__neq (A) F).
------------------------------------------------------------------ assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H84.
------------------------------------------------------------------- exact H83.
------------------------------------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as __TmpHyp.
-------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------- assert (A = F \/ euclidean__axioms.neq A F) as H85.
--------------------------------------------------------------------- exact __TmpHyp.
--------------------------------------------------------------------- destruct H85 as [H85|H85].
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H86.
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H86.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H86 as [H86 H87].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H10).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H87.
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H87.
------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------- destruct H87 as [H87 H88].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__axioms.Col E F A0) -> ((~(euclidean__axioms.Col B C A0)) -> ((euclidean__axioms.BetS c A0 b) -> ((euclidean__defs.CongA b A0 D A0 D B) -> ((euclidean__defs.CongA b A0 D B D A0) -> ((euclidean__defs.CongA D A0 b B D A0) -> ((euclidean__defs.CongA c A0 D A0 D C) -> ((euclidean__defs.CongA c A0 D C D A0) -> ((euclidean__defs.CongA D A0 c C D A0) -> ((euclidean__axioms.Cong c A0 D C) -> ((euclidean__axioms.Cong A0 b B D) -> ((euclidean__axioms.Cong A0 M M D) -> ((euclidean__axioms.BetS A0 M D) -> ((euclidean__axioms.BetS b A0 c) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Col c A0 b) -> ((euclidean__axioms.Col c b A0) -> ((euclidean__axioms.neq A0 b) -> ((euclidean__defs.Par D C A0 b) -> ((euclidean__defs.Par A0 b D C) -> ((euclidean__defs.Par b A0 C D) -> ((euclidean__axioms.Cong A0 b D B) -> ((euclidean__axioms.Cong A0 b C D) -> ((euclidean__axioms.Cong b A0 C D) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__defs.Par b C A0 D) -> ((euclidean__axioms.Cong b C A0 D) -> ((euclidean__defs.Par A0 b C D) -> ((euclidean__defs.Par A0 D b C) -> ((euclidean__defs.PG A0 b C D) -> (euclidean__axioms.neq A0 E)))))))))))))))))))))))))))))))) with (x := A).
--------------------------------------------------------------------------intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
exact H86.

-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------------- exact H18.
-------------------------------------------------------------------------- exact H20.
-------------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------------- exact H26.
-------------------------------------------------------------------------- exact H28.
-------------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------------- exact H45.
-------------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par D C A E) as H88.
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H88.
-------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------- destruct H88 as [H88 H89].
apply (@lemma__collinearparallel2.lemma__collinearparallel2 (D) (C) (E) (F) (A) (E) (H) (H0) (H82) H87).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A b E) as H89.
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H89.
--------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------- destruct H89 as [H89 H90].
apply (@euclidean__tactics.not__nCol__Col (A) (b) (E)).
----------------------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False (A) (b) (E) (H91)).
-----------------------------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair (D) (C) (A) (b) (E) (H69) H88).


-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F b E) as H90.
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H90.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H90 as [H90 H91].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__axioms.Col E F A0) -> ((~(euclidean__axioms.Col B C A0)) -> ((euclidean__axioms.BetS c A0 b) -> ((euclidean__defs.CongA b A0 D A0 D B) -> ((euclidean__defs.CongA b A0 D B D A0) -> ((euclidean__defs.CongA D A0 b B D A0) -> ((euclidean__defs.CongA c A0 D A0 D C) -> ((euclidean__defs.CongA c A0 D C D A0) -> ((euclidean__defs.CongA D A0 c C D A0) -> ((euclidean__axioms.Cong c A0 D C) -> ((euclidean__axioms.Cong A0 b B D) -> ((euclidean__axioms.Cong A0 M M D) -> ((euclidean__axioms.BetS A0 M D) -> ((euclidean__axioms.BetS b A0 c) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Col c A0 b) -> ((euclidean__axioms.Col c b A0) -> ((euclidean__axioms.neq A0 b) -> ((euclidean__defs.Par D C A0 b) -> ((euclidean__defs.Par A0 b D C) -> ((euclidean__defs.Par b A0 C D) -> ((euclidean__axioms.Cong A0 b D B) -> ((euclidean__axioms.Cong A0 b C D) -> ((euclidean__axioms.Cong b A0 C D) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__defs.Par b C A0 D) -> ((euclidean__axioms.Cong b C A0 D) -> ((euclidean__defs.Par A0 b C D) -> ((euclidean__defs.Par A0 D b C) -> ((euclidean__defs.PG A0 b C D) -> ((euclidean__axioms.neq A0 E) -> ((euclidean__defs.Par D C A0 E) -> ((euclidean__axioms.Col A0 b E) -> (euclidean__axioms.Col F b E))))))))))))))))))))))))))))))))))) with (x := A).
-----------------------------------------------------------------------------intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
exact H124.

----------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------- exact H16.
----------------------------------------------------------------------------- exact H18.
----------------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------------- exact H22.
----------------------------------------------------------------------------- exact H24.
----------------------------------------------------------------------------- exact H26.
----------------------------------------------------------------------------- exact H28.
----------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F b) as H91.
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H91.
----------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* Cut *) ((euclidean__axioms.Col b F E) /\ ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))))) as H93.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (b) (E) H90).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col b F E) /\ ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))))) as H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F)))) as H96.
-------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))) as H98.
--------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F)) as H100.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H98.
---------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D C A F) as H86.
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H86.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H86 as [H86 H87].
apply (@lemma__collinearparallel.lemma__collinearparallel (D) (C) (A) (E) (F) (H) (H0) H85).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A b F) as H87.
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H87.
------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------- destruct H87 as [H87 H88].
apply (@euclidean__tactics.not__nCol__Col (A) (b) (F)).
--------------------------------------------------------------------------intro H89.
apply (@euclidean__tactics.Col__nCol__False (A) (b) (F) (H89)).
---------------------------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair (D) (C) (A) (b) (F) (H69) H86).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A F b) as H88.
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H88.
-------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* Cut *) ((euclidean__axioms.Col b A F) /\ ((euclidean__axioms.Col b F A) /\ ((euclidean__axioms.Col F A b) /\ ((euclidean__axioms.Col A F b) /\ (euclidean__axioms.Col F b A))))) as H90.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (b) (F) H87).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col b A F) /\ ((euclidean__axioms.Col b F A) /\ ((euclidean__axioms.Col F A b) /\ ((euclidean__axioms.Col A F b) /\ (euclidean__axioms.Col F b A))))) as H91.
---------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col b F A) /\ ((euclidean__axioms.Col F A b) /\ ((euclidean__axioms.Col A F b) /\ (euclidean__axioms.Col F b A)))) as H93.
----------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col F A b) /\ ((euclidean__axioms.Col A F b) /\ (euclidean__axioms.Col F b A))) as H95.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col A F b) /\ (euclidean__axioms.Col F b A)) as H97.
------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H97.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H89.
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H89.
--------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* Cut *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E A F) /\ (euclidean__axioms.Col A F E))))) as H91.
---------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (A) H0).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E A F) /\ (euclidean__axioms.Col A F E))))) as H92.
----------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E A F) /\ (euclidean__axioms.Col A F E)))) as H94.
------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E A F) /\ (euclidean__axioms.Col A F E))) as H96.
------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ (euclidean__axioms.Col A F E)) as H98.
-------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H99.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F b E) as H90.
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H90.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H90 as [H90 H91].
apply (@euclidean__tactics.not__nCol__Col (F) (b) (E)).
-----------------------------------------------------------------------------intro H92.
apply (@euclidean__tactics.Col__nCol__False (F) (b) (E) (H92)).
------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (F) (b) (E) (H88) (H89) H85).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F b) as H91.
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par b C A D) /\ (euclidean__axioms.Cong b C A D)) as H91.
----------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* Cut *) ((euclidean__axioms.Col b F E) /\ ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))))) as H93.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (b) (E) H90).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col b F E) /\ ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))))) as H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col b E F) /\ ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F)))) as H96.
-------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E F b) /\ ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F))) as H98.
--------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col F E b) /\ (euclidean__axioms.Col E b F)) as H100.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H98.
---------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------- exists b.
split.
------------------------------------------------------------------ exact H80.
------------------------------------------------------------------ exact H83.
Qed.
