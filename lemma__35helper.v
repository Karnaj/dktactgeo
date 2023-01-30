Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__lessthantransitive.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__trichotomy2.
Require Export logic.
Require Export proposition__34.
Definition lemma__35helper : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E B C F) -> ((euclidean__axioms.BetS A D F) -> ((euclidean__axioms.Col A E F) -> (euclidean__axioms.BetS A E F)))).
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
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H3.
- assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H3.
-- exact H0.
-- assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as __TmpHyp.
--- exact H3.
--- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H4.
---- exact __TmpHyp.
---- destruct H4 as [H4 H5].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H6.
----- exact H.
----- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp0.
------ exact H6.
------ assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H7.
------- exact __TmpHyp0.
------- destruct H7 as [H7 H8].
split.
-------- exact H7.
-------- exact H8.
- assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H4.
-- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H4.
--- exact H3.
--- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp.
---- exact H4.
---- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H5.
----- exact __TmpHyp.
----- destruct H5 as [H5 H6].
assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H7.
------ exact H0.
------ assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as __TmpHyp0.
------- exact H7.
------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H8.
-------- exact __TmpHyp0.
-------- destruct H8 as [H8 H9].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10.
--------- exact H.
--------- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp1.
---------- exact H10.
---------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
----------- exact __TmpHyp1.
----------- destruct H11 as [H11 H12].
split.
------------ exact H8.
------------ exact H9.
-- assert (* Cut *) (euclidean__defs.Par A B D C) as H5.
--- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H7.
----- exact H3.
----- destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H9.
------ apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H7).
------ assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
exact H12.
--- assert (* Cut *) (euclidean__defs.Par E B F C) as H6.
---- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H6.
----- exact H4.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H8.
------ exact H3.
------ destruct H8 as [H8 H9].
assert (* Cut *) ((euclidean__defs.Par B E C F) /\ ((euclidean__defs.Par E B F C) /\ (euclidean__defs.Par B E F C))) as H10.
------- apply (@lemma__parallelflip.lemma__parallelflip (E) (B) (C) (F) H6).
------- assert (* AndElim *) ((euclidean__defs.Par B E C F) /\ ((euclidean__defs.Par E B F C) /\ (euclidean__defs.Par B E F C))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Par E B F C) /\ (euclidean__defs.Par B E F C)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
exact H13.
---- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H7.
----- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H7.
------ exact H4.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H9.
------- exact H3.
------- destruct H9 as [H9 H10].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H11.
-------- apply (@proposition__34.proposition__34 (A) (D) (B) (C) H).
-------- assert (* AndElim *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
exact H12.
----- assert (* Cut *) (euclidean__axioms.Cong E F B C) as H8.
------ assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H8.
------- exact H4.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10.
-------- exact H3.
-------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H12.
--------- apply (@proposition__34.proposition__34 (E) (F) (B) (C) H0).
--------- assert (* AndElim *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B)))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B)) as H19.
------------- exact H18.
------------- destruct H19 as [H19 H20].
exact H13.
------ assert (* Cut *) (euclidean__axioms.Cong B C E F) as H9.
------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H9.
-------- exact H4.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
--------- exact H3.
--------- destruct H11 as [H11 H12].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (E) (F) (C) H8).
------- assert (* Cut *) (euclidean__axioms.Cong A D E F) as H10.
-------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H10.
--------- exact H4.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H12.
---------- exact H3.
---------- destruct H12 as [H12 H13].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (D) (B) (C) (E) (F) (H7) H9).
-------- assert (* Cut *) (euclidean__axioms.Col A D F) as H11.
--------- right.
right.
right.
right.
left.
exact H1.
--------- assert (* Cut *) (euclidean__axioms.Col F A E) as H12.
---------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H12.
----------- exact H4.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
------------ exact H3.
------------ destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H16.
------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (F) H2).
------------- assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A)))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
exact H21.
---------- assert (* Cut *) (euclidean__axioms.Col F A D) as H13.
----------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H13.
------------ exact H4.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
------------- exact H3.
------------- destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H17.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (F) H11).
-------------- assert (* AndElim *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H22.
----------- assert (* Cut *) (euclidean__axioms.neq A F) as H14.
------------ assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H14.
------------- exact H4.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16.
-------------- exact H3.
-------------- destruct H16 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H18.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (F) H1).
--------------- assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H22.
------------ assert (* Cut *) (euclidean__axioms.neq F A) as H15.
------------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H15.
-------------- exact H4.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H17.
--------------- exact H3.
--------------- destruct H17 as [H17 H18].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (F) H14).
------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H16.
-------------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H16.
--------------- exact H4.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H18.
---------------- exact H3.
---------------- destruct H18 as [H18 H19].
apply (@euclidean__tactics.not__nCol__Col (A) (E) (D)).
-----------------intro H20.
apply (@euclidean__tactics.Col__nCol__False (A) (E) (D) (H20)).
------------------apply (@lemma__collinear4.lemma__collinear4 (F) (A) (E) (D) (H12) (H13) H15).


-------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H17.
--------------- assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H17.
---------------- exact H4.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H19.
----------------- exact H3.
----------------- destruct H19 as [H19 H20].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (B) (C) (D) H).
--------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H18.
---------------- exact H17.
---------------- destruct H18 as [M H18].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H21.
------------------ exact H4.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H23.
------------------- exact H3.
------------------- destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__axioms.BetS D M B) as H25.
-------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (D) H20).
-------------------- assert (* Cut *) (euclidean__axioms.BetS C M A) as H26.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (C) H19).
--------------------- assert (* Cut *) (euclidean__axioms.BetS B M D) as H27.
---------------------- exact H20.
---------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS E m C) /\ (euclidean__axioms.BetS B m F)) as H28.
----------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (E) (B) (C) (F) H0).
----------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS E m C) /\ (euclidean__axioms.BetS B m F))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [m H29].
assert (* AndElim *) ((euclidean__axioms.BetS E m C) /\ (euclidean__axioms.BetS B m F)) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS F m B) as H32.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (m) (F) H31).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS B m F) as H33.
--------------------------- exact H31.
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H34.
----------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H24).
----------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
exact H35.
---------------------------- assert (* Cut *) (euclidean__axioms.Col A D F) as H35.
----------------------------- exact H11.
----------------------------- assert (* Cut *) (A = A) as H36.
------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------ assert (* Cut *) (euclidean__axioms.Col A D A) as H37.
------------------------------- right.
left.
exact H36.
------------------------------- assert (* Cut *) (euclidean__axioms.nCol A F B) as H38.
-------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (F) (B)).
---------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (F) (B)).
----------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (D) (B) (A) (F) (H34) (H37) (H35) H14).


-------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS B Q F) /\ (euclidean__axioms.BetS A M Q)) as H39.
--------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (B) (A) (D) (M) (F) (H27) (H1) H38).
--------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS B Q F) /\ (euclidean__axioms.BetS A M Q))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [Q H40].
assert (* AndElim *) ((euclidean__axioms.BetS B Q F) /\ (euclidean__axioms.BetS A M Q)) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
assert (* Cut *) (euclidean__axioms.Col A M Q) as H43.
------------------------------------ right.
right.
right.
right.
left.
exact H42.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col A M C) as H44.
------------------------------------- right.
right.
right.
right.
left.
exact H19.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A Q) as H45.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M A Q) /\ ((euclidean__axioms.Col M Q A) /\ ((euclidean__axioms.Col Q A M) /\ ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A))))) as H45.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (M) (Q) H43).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M A Q) /\ ((euclidean__axioms.Col M Q A) /\ ((euclidean__axioms.Col Q A M) /\ ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A))))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col M Q A) /\ ((euclidean__axioms.Col Q A M) /\ ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A)))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col Q A M) /\ ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A))) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A)) as H52.
------------------------------------------- exact H51.
------------------------------------------- destruct H52 as [H52 H53].
exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A C) as H46.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H46.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (M) (C) H44).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A)))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A)) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
exact H47.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H47.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H47.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (Q) H42).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q)) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
exact H50.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H48.
----------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (M) H47).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A Q C) as H49.
------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (Q) (C)).
-------------------------------------------intro H49.
apply (@euclidean__tactics.Col__nCol__False (A) (Q) (C) (H49)).
--------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (A) (Q) (C) (H45) (H46) H48).


------------------------------------------ assert (* Cut *) (A = A) as H50.
------------------------------------------- exact H36.
------------------------------------------- assert (* Cut *) (C = C) as H51.
-------------------------------------------- apply (@logic.eq__refl (Point) C).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A A) as H52.
--------------------------------------------- right.
right.
left.
exact H50.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C C B) as H53.
---------------------------------------------- left.
exact H51.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H54.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H54.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (Q) H42).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q)) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
exact H14.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F A) as H55.
------------------------------------------------ exact H15.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H56.
------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H56.
-------------------------------------------------- exact H6.
-------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--------------------------------------------------- exact H56.
--------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H57.
---------------------------------------------------- exact __TmpHyp.
---------------------------------------------------- destruct H57 as [x H57].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [x0 H58].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [x1 H59].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H60.
------------------------------------------------------- exact H59.
------------------------------------------------------- destruct H60 as [x2 H60].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [x3 H61].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H74.
--------------------------------------------------------------- exact H73.
--------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H76.
---------------------------------------------------------------- exact H75.
---------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H78.
----------------------------------------------------------------- exact H77.
----------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H80.
------------------------------------------------------------------ exact H79.
------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H82.
------------------------------------------------------------------- exact H5.
------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H83.
--------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------- destruct H83 as [x4 H83].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H84.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- destruct H84 as [x5 H84].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H85.
----------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------- destruct H85 as [x6 H85].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H86.
------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------ destruct H86 as [x7 H86].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H87.
------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------- destruct H87 as [x8 H87].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H88.
-------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H90.
--------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H92.
---------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H94.
----------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H96.
------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H98.
------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H100.
-------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H102.
--------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H104.
---------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H106.
----------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H108.
------------------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H109.
-------------------------------------------------------------------------------------- exact __TmpHyp1.
-------------------------------------------------------------------------------------- destruct H109 as [x9 H109].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H110.
--------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------- destruct H110 as [x10 H110].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H111.
---------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------- destruct H111 as [x11 H111].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H112.
----------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------- destruct H112 as [x12 H112].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H113.
------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------ destruct H113 as [x13 H113].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H114.
------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H116.
-------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H118.
--------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H120.
---------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H122.
----------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H124.
------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H126.
------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H128.
-------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H130.
--------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H132.
---------------------------------------------------------------------------------------------------- exact H131.
---------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H134.
----------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H135.
------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------------- destruct H135 as [x14 H135].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H136.
-------------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------------- destruct H136 as [x15 H136].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H137.
--------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------- destruct H137 as [x16 H137].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H138.
---------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------- destruct H138 as [x17 H138].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H139.
----------------------------------------------------------------------------------------------------------- exact H138.
----------------------------------------------------------------------------------------------------------- destruct H139 as [x18 H139].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H140.
------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H142.
------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H144.
-------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H146.
--------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H148.
---------------------------------------------------------------------------------------------------------------- exact H147.
---------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H150.
----------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H152.
------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------ destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H154.
------------------------------------------------------------------------------------------------------------------- exact H153.
------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H156.
-------------------------------------------------------------------------------------------------------------------- exact H155.
-------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H158.
--------------------------------------------------------------------------------------------------------------------- exact H157.
--------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H160.
---------------------------------------------------------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H161.
------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------ destruct H161 as [x19 H161].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H162.
------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x20 H162].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H163.
-------------------------------------------------------------------------------------------------------------------------- exact H162.
-------------------------------------------------------------------------------------------------------------------------- destruct H163 as [x21 H163].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H164.
--------------------------------------------------------------------------------------------------------------------------- exact H163.
--------------------------------------------------------------------------------------------------------------------------- destruct H164 as [x22 H164].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H165.
---------------------------------------------------------------------------------------------------------------------------- exact H164.
---------------------------------------------------------------------------------------------------------------------------- destruct H165 as [x23 H165].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H166.
----------------------------------------------------------------------------------------------------------------------------- exact H165.
----------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------ exact H167.
------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H170.
------------------------------------------------------------------------------------------------------------------------------- exact H169.
------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------- exact H171.
-------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------- exact H173.
--------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H176.
---------------------------------------------------------------------------------------------------------------------------------- exact H175.
---------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------- exact H177.
----------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H180.
------------------------------------------------------------------------------------------------------------------------------------ exact H179.
------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H182.
------------------------------------------------------------------------------------------------------------------------------------- exact H181.
------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H184.
-------------------------------------------------------------------------------------------------------------------------------------- exact H183.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H186.
--------------------------------------------------------------------------------------------------------------------------------------- exact H23.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
---------------------------------------------------------------------------------------------------------------------------------------- exact H186.
---------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H187.
----------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x24 H187].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H188.
------------------------------------------------------------------------------------------------------------------------------------------ exact H187.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H188 as [x25 H188].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H189.
------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [x26 H189].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H190.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [x27 H190].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H191.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [x28 H191].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H194.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H200.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H202.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H204.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H206.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H207.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
exact H168.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H57.
-------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H56).
-------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet F A C B)) as H58.
--------------------------------------------------- intro H58.
assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p)))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p))))) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [p H60].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p)))) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p)) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* Cut *) (euclidean__axioms.Col A D F) as H67.
--------------------------------------------------------- exact H35.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A D) as H68.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H68.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (F) H67).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)))) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))) as H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)) as H75.
--------------------------------------------------------------- exact H74.
--------------------------------------------------------------- destruct H75 as [H75 H76].
exact H73.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H69.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H69.
------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (F) H1).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F)) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
exact H72.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D p) as H70.
------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (D) (p)).
-------------------------------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (p) (H70)).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (A) (D) (p) (H68) (H65) H61).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C p) as H71.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H71.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (p) H66).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H72.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)))) as H74.
---------------------------------------------------------------- exact H73.
---------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))) as H76.
----------------------------------------------------------------- exact H75.
----------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)) as H78.
------------------------------------------------------------------ exact H77.
------------------------------------------------------------------ destruct H78 as [H78 H79].
exact H72.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H72.
-------------------------------------------------------------- exists p.
split.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H56.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- exact H71.
-------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H73.
--------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H73.
---------------------------------------------------------------- exact H6.
---------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H74.
------------------------------------------------------------------ exact __TmpHyp.
------------------------------------------------------------------ destruct H74 as [x H74].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H75.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H75 as [x0 H75].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H76.
-------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------- destruct H76 as [x1 H76].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [x2 H77].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H78.
---------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------- destruct H78 as [x3 H78].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H79.
----------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H81.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H85.
-------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H89.
---------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H93.
------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H95.
------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H97.
-------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H99.
--------------------------------------------------------------------------------- exact H5.
--------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H100.
----------------------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------------------- destruct H100 as [x4 H100].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H101.
------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------ destruct H101 as [x5 H101].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H102.
------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------- destruct H102 as [x6 H102].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H103.
-------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------- destruct H103 as [x7 H103].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H104.
--------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------- destruct H104 as [x8 H104].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H105.
---------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H107.
----------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H109.
------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H111.
------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H113.
-------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H115.
--------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H117.
---------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H119.
----------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H121.
------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H123.
------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H125.
-------------------------------------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
--------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H126.
---------------------------------------------------------------------------------------------------- exact __TmpHyp1.
---------------------------------------------------------------------------------------------------- destruct H126 as [x9 H126].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H127.
----------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------- destruct H127 as [x10 H127].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H128.
------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------ destruct H128 as [x11 H128].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H129.
------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------- destruct H129 as [x12 H129].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H130.
-------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------- destruct H130 as [x13 H130].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H131.
--------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H133.
---------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H135.
----------------------------------------------------------------------------------------------------------- exact H134.
----------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H137.
------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------ destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H139.
------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H141.
-------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H143.
--------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H145.
---------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H147.
----------------------------------------------------------------------------------------------------------------- exact H146.
----------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H149.
------------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------------ destruct H149 as [H149 H150].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H151.
------------------------------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
-------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H152.
--------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
--------------------------------------------------------------------------------------------------------------------- destruct H152 as [x14 H152].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H153.
---------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------- destruct H153 as [x15 H153].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H154.
----------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------- destruct H154 as [x16 H154].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H155.
------------------------------------------------------------------------------------------------------------------------ exact H154.
------------------------------------------------------------------------------------------------------------------------ destruct H155 as [x17 H155].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H156.
------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------- destruct H156 as [x18 H156].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H157.
-------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H159.
--------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H161.
---------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H163.
----------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H167.
------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H171.
--------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H173.
---------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H175.
----------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------- exact H177.
------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H178.
-------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [x19 H178].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H179.
--------------------------------------------------------------------------------------------------------------------------------------- exact H178.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [x20 H179].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H180.
---------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [x21 H180].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H181.
----------------------------------------------------------------------------------------------------------------------------------------- exact H180.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [x22 H181].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------ exact H181.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H182 as [x23 H182].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H199.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H201.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H203.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H203.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [x24 H204].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [x25 H205].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [x26 H206].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H207.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [x27 H207].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H208.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [x28 H208].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H225.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
exact H199.
--------------------------------------------------------------- apply (@H73 H72).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F Q B) as H59.
---------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (Q) (F) H41).
---------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H60.
----------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H60.
------------------------------------------------------ exact H6.
------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------------------------------------------- exact H60.
------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H61.
-------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------- destruct H61 as [x H61].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [x0 H62].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [x1 H63].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [x2 H64].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [x3 H65].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H72.
---------------------------------------------------------------- exact H71.
---------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H82.
--------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H84.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H86.
----------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H87.
------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------- destruct H87 as [x4 H87].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H88.
-------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------- destruct H88 as [x5 H88].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H89.
--------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------- destruct H89 as [x6 H89].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H90.
---------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------- destruct H90 as [x7 H90].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [x8 H91].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H92.
------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H96.
-------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H98.
--------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H100.
---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H102.
----------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H104.
------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H106.
------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H108.
-------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H110.
--------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H112.
---------------------------------------------------------------------------------------- exact H22.
---------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H113.
------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------ destruct H113 as [x9 H113].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H114.
------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------- destruct H114 as [x10 H114].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H115.
-------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------- destruct H115 as [x11 H115].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H116.
--------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------- destruct H116 as [x12 H116].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H117.
---------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------- destruct H117 as [x13 H117].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H118.
----------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H120.
------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------ destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H122.
------------------------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H124.
-------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H126.
--------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H128.
---------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H130.
----------------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H132.
------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H134.
------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H136.
-------------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H138.
--------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H139.
----------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------- destruct H139 as [x14 H139].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H140.
------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------ destruct H140 as [x15 H140].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H141.
------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------- destruct H141 as [x16 H141].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H142.
-------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------- destruct H142 as [x17 H142].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H143.
--------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------- destruct H143 as [x18 H143].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H144.
---------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H146.
----------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H148.
------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------ destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H150.
------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H152.
-------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H154.
--------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H156.
---------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H158.
----------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H160.
------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------ destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H162.
------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H164.
-------------------------------------------------------------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------- exact H164.
--------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H165.
---------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------- destruct H165 as [x19 H165].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H166.
----------------------------------------------------------------------------------------------------------------------------- exact H165.
----------------------------------------------------------------------------------------------------------------------------- destruct H166 as [x20 H166].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------ exact H166.
------------------------------------------------------------------------------------------------------------------------------ destruct H167 as [x21 H167].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------- exact H167.
------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [x22 H168].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [x23 H169].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H170.
--------------------------------------------------------------------------------------------------------------------------------- exact H169.
--------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H172.
---------------------------------------------------------------------------------------------------------------------------------- exact H171.
---------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H174.
----------------------------------------------------------------------------------------------------------------------------------- exact H173.
----------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H176.
------------------------------------------------------------------------------------------------------------------------------------ exact H175.
------------------------------------------------------------------------------------------------------------------------------------ destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H178.
------------------------------------------------------------------------------------------------------------------------------------- exact H177.
------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H180.
-------------------------------------------------------------------------------------------------------------------------------------- exact H179.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H182.
--------------------------------------------------------------------------------------------------------------------------------------- exact H181.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H184.
---------------------------------------------------------------------------------------------------------------------------------------- exact H183.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H186.
----------------------------------------------------------------------------------------------------------------------------------------- exact H185.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H188.
------------------------------------------------------------------------------------------------------------------------------------------ exact H187.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H188 as [H188 H189].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H190.
------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H191.
--------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [x24 H191].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [x25 H192].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H193.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [x26 H193].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H194 as [x27 H194].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [x28 H195].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H196.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H198.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H200.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H202.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H203.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H212.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
exact H186.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C Q) as H61.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col Q A C) /\ ((euclidean__axioms.Col Q C A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A))))) as H61.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (Q) (C) H49).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q A C) /\ ((euclidean__axioms.Col Q C A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A))))) as H62.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col Q C A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A)))) as H64.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A)) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS A Q C) as H62.
------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (F) (A) (C) (B) (A) (C) (Q) (H52) (H53) (H55) (H57) (H55) (H57) (H58) (H59) H61).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C Q A) as H63.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (Q) (C) H62).
-------------------------------------------------------- assert (* Cut *) (~(A = E)) as H64.
--------------------------------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.Cong A F A F) as H65.
---------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) F).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F E F) as H66.
----------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> (euclidean__axioms.Cong A0 F E F))))))))))))))))))))))))))))))))))))))))) with (x := A).
------------------------------------------------------------intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
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
exact H104.

------------------------------------------------------------ exact H64.
------------------------------------------------------------ exact H.
------------------------------------------------------------ exact H1.
------------------------------------------------------------ exact H2.
------------------------------------------------------------ exact H23.
------------------------------------------------------------ exact H24.
------------------------------------------------------------ exact H5.
------------------------------------------------------------ exact H7.
------------------------------------------------------------ exact H10.
------------------------------------------------------------ exact H11.
------------------------------------------------------------ exact H12.
------------------------------------------------------------ exact H13.
------------------------------------------------------------ exact H14.
------------------------------------------------------------ exact H15.
------------------------------------------------------------ exact H16.
------------------------------------------------------------ exact H19.
------------------------------------------------------------ exact H26.
------------------------------------------------------------ exact H34.
------------------------------------------------------------ exact H35.
------------------------------------------------------------ exact H36.
------------------------------------------------------------ exact H37.
------------------------------------------------------------ exact H38.
------------------------------------------------------------ exact H42.
------------------------------------------------------------ exact H43.
------------------------------------------------------------ exact H44.
------------------------------------------------------------ exact H45.
------------------------------------------------------------ exact H46.
------------------------------------------------------------ exact H47.
------------------------------------------------------------ exact H48.
------------------------------------------------------------ exact H49.
------------------------------------------------------------ exact H50.
------------------------------------------------------------ exact H52.
------------------------------------------------------------ exact H54.
------------------------------------------------------------ exact H55.
------------------------------------------------------------ exact H58.
------------------------------------------------------------ exact H60.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ exact H62.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ exact H65.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F A D) as H67.
------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (A) (D) (F) H10).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A F A D) as H68.
------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__axioms.Cong E F A0 D) -> (euclidean__axioms.Cong A0 F A0 D))))))))))))))))))))))))))))))))))))))))))) with (x := A).
--------------------------------------------------------------intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
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
exact H108.

-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- exact H.
-------------------------------------------------------------- exact H1.
-------------------------------------------------------------- exact H2.
-------------------------------------------------------------- exact H23.
-------------------------------------------------------------- exact H24.
-------------------------------------------------------------- exact H5.
-------------------------------------------------------------- exact H7.
-------------------------------------------------------------- exact H10.
-------------------------------------------------------------- exact H11.
-------------------------------------------------------------- exact H12.
-------------------------------------------------------------- exact H13.
-------------------------------------------------------------- exact H14.
-------------------------------------------------------------- exact H15.
-------------------------------------------------------------- exact H16.
-------------------------------------------------------------- exact H19.
-------------------------------------------------------------- exact H26.
-------------------------------------------------------------- exact H34.
-------------------------------------------------------------- exact H35.
-------------------------------------------------------------- exact H36.
-------------------------------------------------------------- exact H37.
-------------------------------------------------------------- exact H38.
-------------------------------------------------------------- exact H42.
-------------------------------------------------------------- exact H43.
-------------------------------------------------------------- exact H44.
-------------------------------------------------------------- exact H45.
-------------------------------------------------------------- exact H46.
-------------------------------------------------------------- exact H47.
-------------------------------------------------------------- exact H48.
-------------------------------------------------------------- exact H49.
-------------------------------------------------------------- exact H50.
-------------------------------------------------------------- exact H52.
-------------------------------------------------------------- exact H54.
-------------------------------------------------------------- exact H55.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- exact H60.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- exact H62.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- exact H67.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A F) as H69.
-------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__axioms.Cong E F A0 D) -> ((euclidean__axioms.Cong A0 F A0 D) -> (euclidean__axioms.Cong A0 D A0 F)))))))))))))))))))))))))))))))))))))))))))) with (x := A).
---------------------------------------------------------------intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
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
exact H76.

--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- exact H.
--------------------------------------------------------------- exact H1.
--------------------------------------------------------------- exact H2.
--------------------------------------------------------------- exact H23.
--------------------------------------------------------------- exact H24.
--------------------------------------------------------------- exact H5.
--------------------------------------------------------------- exact H7.
--------------------------------------------------------------- exact H10.
--------------------------------------------------------------- exact H11.
--------------------------------------------------------------- exact H12.
--------------------------------------------------------------- exact H13.
--------------------------------------------------------------- exact H14.
--------------------------------------------------------------- exact H15.
--------------------------------------------------------------- exact H16.
--------------------------------------------------------------- exact H19.
--------------------------------------------------------------- exact H26.
--------------------------------------------------------------- exact H34.
--------------------------------------------------------------- exact H35.
--------------------------------------------------------------- exact H36.
--------------------------------------------------------------- exact H37.
--------------------------------------------------------------- exact H38.
--------------------------------------------------------------- exact H42.
--------------------------------------------------------------- exact H43.
--------------------------------------------------------------- exact H44.
--------------------------------------------------------------- exact H45.
--------------------------------------------------------------- exact H46.
--------------------------------------------------------------- exact H47.
--------------------------------------------------------------- exact H48.
--------------------------------------------------------------- exact H49.
--------------------------------------------------------------- exact H50.
--------------------------------------------------------------- exact H52.
--------------------------------------------------------------- exact H54.
--------------------------------------------------------------- exact H55.
--------------------------------------------------------------- exact H58.
--------------------------------------------------------------- exact H60.
--------------------------------------------------------------- exact H61.
--------------------------------------------------------------- exact H62.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- exact H65.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- exact H68.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A D) as H70.
--------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) D).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D A F) as H71.
---------------------------------------------------------------- exists D.
split.
----------------------------------------------------------------- exact H1.
----------------------------------------------------------------- exact H70.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A F A F) as H72.
----------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (A) (D) (A) (F) (A) (F) (H71) H69).
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt A F A F)) as H73.
------------------------------------------------------------------ apply (@lemma__trichotomy2.lemma__trichotomy2 (A) (F) (A) (F) H72).
------------------------------------------------------------------ apply (@H73 H72).
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A F E)) as H65.
---------------------------------------------------------- intro H65.
assert (* Cut *) (euclidean__axioms.BetS E F A) as H66.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (F) (E) H65).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D C) as H67.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H67.
------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (D) (C) H5).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C))) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)) as H72.
---------------------------------------------------------------- exact H71.
---------------------------------------------------------------- destruct H72 as [H72 H73].
exact H70.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A D E) as H68.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H68.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (D) H16).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H69.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)))) as H71.
---------------------------------------------------------------- exact H70.
---------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))) as H73.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
exact H75.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H69.
-------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (C)).
---------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (C)).
----------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (D) (C) (A) (E) (H67) (H37) (H68) H64).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A E) as H70.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H70.
---------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (C) H69).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H71.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)))) as H73.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))) as H75.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)) as H77.
-------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H75.
--------------------------------------------------------------- assert (* Cut *) (exists (r: euclidean__axioms.Point), (euclidean__axioms.BetS C r F) /\ (euclidean__axioms.BetS E r Q)) as H71.
---------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (C) (E) (A) (Q) (F) (H63) (H66) H70).
---------------------------------------------------------------- assert (exists r: euclidean__axioms.Point, ((euclidean__axioms.BetS C r F) /\ (euclidean__axioms.BetS E r Q))) as H72.
----------------------------------------------------------------- exact H71.
----------------------------------------------------------------- destruct H72 as [r H72].
assert (* AndElim *) ((euclidean__axioms.BetS C r F) /\ (euclidean__axioms.BetS E r Q)) as H73.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H73 as [H73 H74].
assert (* Cut *) (euclidean__axioms.BetS Q r E) as H75.
------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (r) (Q) H74).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B F) as H76.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol E B C)))) as H76.
--------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (E) (B) (F) (C) H6).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol E B C)))) as H77.
---------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol E B C))) as H79.
----------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol E B C)) as H81.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
exact H77.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B E) as H77.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E F) /\ ((euclidean__axioms.nCol B F E) /\ ((euclidean__axioms.nCol F E B) /\ ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E))))) as H77.
---------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (B) (F) H76).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B E F) /\ ((euclidean__axioms.nCol B F E) /\ ((euclidean__axioms.nCol F E B) /\ ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E))))) as H78.
----------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol B F E) /\ ((euclidean__axioms.nCol F E B) /\ ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E)))) as H80.
------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol F E B) /\ ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E))) as H82.
------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E)) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
--------------------------------------------------------------------- assert (* Cut *) (exists (H78: euclidean__axioms.Point), (euclidean__axioms.BetS E H78 B) /\ (euclidean__axioms.BetS F r H78)) as H78.
---------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (E) (F) (Q) (r) (B) (H74) (H59) H77).
---------------------------------------------------------------------- assert (exists H79: euclidean__axioms.Point, ((euclidean__axioms.BetS E H79 B) /\ (euclidean__axioms.BetS F r H79))) as H80.
----------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------- destruct H80 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.BetS E H79 B) /\ (euclidean__axioms.BetS F r H79)) as H81.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* Cut *) (euclidean__axioms.Col E H79 B) as H83.
------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H81.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F r H79) as H84.
-------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H82.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B H79) as H85.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H79 E B) /\ ((euclidean__axioms.Col H79 B E) /\ ((euclidean__axioms.Col B E H79) /\ ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E))))) as H85.
---------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (H79) (B) H83).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H79 E B) /\ ((euclidean__axioms.Col H79 B E) /\ ((euclidean__axioms.Col B E H79) /\ ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E))))) as H86.
----------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col H79 B E) /\ ((euclidean__axioms.Col B E H79) /\ ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E)))) as H88.
------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------ destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col B E H79) /\ ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E))) as H90.
------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E)) as H92.
-------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------- destruct H92 as [H92 H93].
exact H92.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C r F) as H86.
---------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H73.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r F C) as H87.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r C F) /\ ((euclidean__axioms.Col r F C) /\ ((euclidean__axioms.Col F C r) /\ ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C))))) as H87.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (r) (F) H86).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col r C F) /\ ((euclidean__axioms.Col r F C) /\ ((euclidean__axioms.Col F C r) /\ ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C))))) as H88.
------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col r F C) /\ ((euclidean__axioms.Col F C r) /\ ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C)))) as H90.
-------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col F C r) /\ ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C))) as H92.
--------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C)) as H94.
---------------------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H90.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r F H79) as H88.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r F H79) /\ ((euclidean__axioms.Col r H79 F) /\ ((euclidean__axioms.Col H79 F r) /\ ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F))))) as H88.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (r) (H79) H84).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r F H79) /\ ((euclidean__axioms.Col r H79 F) /\ ((euclidean__axioms.Col H79 F r) /\ ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F))))) as H89.
-------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col r H79 F) /\ ((euclidean__axioms.Col H79 F r) /\ ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F)))) as H91.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col H79 F r) /\ ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F))) as H93.
---------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F)) as H95.
----------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H89.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq r F) as H89.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq r F) /\ ((euclidean__axioms.neq C r) /\ (euclidean__axioms.neq C F))) as H89.
-------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (r) (F) H73).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq r F) /\ ((euclidean__axioms.neq C r) /\ (euclidean__axioms.neq C F))) as H90.
--------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.neq C r) /\ (euclidean__axioms.neq C F)) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
exact H90.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C H79) as H90.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (C) (H79)).
---------------------------------------------------------------------------------intro H90.
apply (@euclidean__tactics.Col__nCol__False (F) (C) (H79) (H90)).
----------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (r) (F) (C) (H79) (H87) (H88) H89).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H91.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F)))))) as H91.
---------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (F) (B) (E) H77).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F)))))) as H92.
----------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F))))) as H94.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F)))) as H96.
------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F))) as H98.
-------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F)) as H100.
--------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H94.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H92.
---------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H91).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F C) as H93.
----------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H93.
------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H94.
-------------------------------------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------------------------------------- destruct H94 as [x H94].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [x0 H95].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H96.
---------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------- destruct H96 as [x1 H96].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H97.
----------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------- destruct H97 as [x2 H97].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H98.
------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------ destruct H98 as [x3 H98].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H99.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H101.
-------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H103.
--------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H105.
---------------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H107.
----------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H109.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H111.
------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H113.
-------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H115.
--------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H117.
---------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H119.
----------------------------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H120.
------------------------------------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------------------------------------- destruct H120 as [x4 H120].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H121.
-------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------- destruct H121 as [x5 H121].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H122.
--------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------- destruct H122 as [x6 H122].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H123.
---------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------- destruct H123 as [x7 H123].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H124.
----------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------- destruct H124 as [x8 H124].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H125.
------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H127.
------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H129.
-------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H131.
--------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H133.
---------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H135.
----------------------------------------------------------------------------------------------------------------- exact H134.
----------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H137.
------------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------------ destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H139.
------------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H141.
-------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H143.
--------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H145.
---------------------------------------------------------------------------------------------------------------------- exact H22.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H146.
------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------------------------------------ destruct H146 as [x9 H146].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H147.
------------------------------------------------------------------------------------------------------------------------- exact H146.
------------------------------------------------------------------------------------------------------------------------- destruct H147 as [x10 H147].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------- destruct H148 as [x11 H148].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H149.
--------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------- destruct H149 as [x12 H149].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H150.
---------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------- destruct H150 as [x13 H150].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H151.
----------------------------------------------------------------------------------------------------------------------------- exact H150.
----------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H153.
------------------------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------------------------ destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H155.
------------------------------------------------------------------------------------------------------------------------------- exact H154.
------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H157.
-------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H159.
--------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H161.
---------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H163.
----------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H165.
------------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H167.
------------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H169.
-------------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H171.
--------------------------------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------------------------------------- exact H171.
---------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H172.
----------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [x14 H172].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------ exact H172.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H173 as [x15 H173].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H174.
------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [x16 H174].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [x17 H175].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H176.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [x18 H176].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H179.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H181.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H198.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [x19 H198].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [x20 H199].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H199.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H200 as [x21 H200].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [x22 H201].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [x23 H202].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H205.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H207.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H221 as [H221 H222].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H224.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [x24 H224].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H225.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [x25 H225].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [x26 H226].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H227 as [x27 H227].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [x28 H228].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H231.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H233.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H235.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H237 as [H237 H238].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
exact H101.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E B F C) as H94.
------------------------------------------------------------------------------------ exists H79.
split.
------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.Meet E B F C)) as H95.
------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H95.
-------------------------------------------------------------------------------------- exact H6.
-------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H96.
---------------------------------------------------------------------------------------- exact __TmpHyp.
---------------------------------------------------------------------------------------- destruct H96 as [x H96].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H97.
----------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------- destruct H97 as [x0 H97].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H98.
------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------ destruct H98 as [x1 H98].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H99.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- destruct H99 as [x2 H99].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H100.
-------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------- destruct H100 as [x3 H100].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H101.
--------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H103.
---------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H105.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H107.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H109.
------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H111.
-------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H113.
--------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H115.
---------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H117.
----------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H119.
------------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H121.
------------------------------------------------------------------------------------------------------- exact H5.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H122.
--------------------------------------------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------------------------------------------- destruct H122 as [x4 H122].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H123.
---------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------- destruct H123 as [x5 H123].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H124.
----------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------- destruct H124 as [x6 H124].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H125.
------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------ destruct H125 as [x7 H125].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H126.
------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------- destruct H126 as [x8 H126].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H127.
-------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H129.
--------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H131.
---------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H133.
----------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H135.
------------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H137.
------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H139.
-------------------------------------------------------------------------------------------------------------------- exact H138.
-------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H141.
--------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H143.
---------------------------------------------------------------------------------------------------------------------- exact H142.
---------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H145.
----------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H147.
------------------------------------------------------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------------------------------------------------------------- exact H147.
------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
-------------------------------------------------------------------------------------------------------------------------- destruct H148 as [x9 H148].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H149.
--------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------- destruct H149 as [x10 H149].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H150.
---------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------- destruct H150 as [x11 H150].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H151.
----------------------------------------------------------------------------------------------------------------------------- exact H150.
----------------------------------------------------------------------------------------------------------------------------- destruct H151 as [x12 H151].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H152.
------------------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [x13 H152].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H153.
------------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H155.
-------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H157.
--------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H159.
---------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H161.
----------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H163.
------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------ destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H165.
------------------------------------------------------------------------------------------------------------------------------------- exact H164.
------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H167.
-------------------------------------------------------------------------------------------------------------------------------------- exact H166.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H169.
--------------------------------------------------------------------------------------------------------------------------------------- exact H168.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H171.
---------------------------------------------------------------------------------------------------------------------------------------- exact H170.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H173.
----------------------------------------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------------------------------------------ exact H173.
------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H174.
------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [x14 H174].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [x15 H175].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H176.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [x16 H176].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [x17 H177].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [x18 H178].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H181.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H183.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H185.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H187.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H189.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H195.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H197.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H199.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H200 as [x19 H200].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [x20 H201].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [x21 H202].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [x22 H203].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H204.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [x23 H204].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H219 as [H219 H220].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H225.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [x24 H226].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H227 as [x25 H227].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [x26 H228].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [x27 H229].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H230.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [x28 H230].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H231.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H233.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H235.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H235 as [H235 H236].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H237 as [H237 H238].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H239.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H241.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H243.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H245.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H247.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H246.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H247 as [H247 H248].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H249 as [H249 H250].
exact H117.
------------------------------------------------------------------------------------- apply (@H95 H94).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H66.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H66.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (E) H12).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
exact H67.
----------------------------------------------------------- assert (* Cut *) ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as H67.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS A E F) as H68.
------------------------------------------------------------- assert (* Cut *) ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- assert (* Cut *) ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as __TmpHyp.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- assert (A = F \/ (A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F))))) as H69.
---------------------------------------------------------------- exact __TmpHyp.
---------------------------------------------------------------- destruct H69 as [H69|H69].
----------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H70.
------------------------------------------------------------------ intro H70.
assert (* Cut *) (euclidean__axioms.BetS A D A) as H71.
------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((~(A0 = E)) -> ((~(euclidean__axioms.BetS A0 F E)) -> ((euclidean__axioms.Col A0 F E) -> ((~(euclidean__axioms.BetS A0 E F)) -> (euclidean__axioms.BetS A0 D A0)))))))))))))))))))))))))))))))))))))))))))) with (x := A).
--------------------------------------------------------------------intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
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
exact H72.

-------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------- exact H.
-------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------- exact H5.
-------------------------------------------------------------------- exact H7.
-------------------------------------------------------------------- exact H10.
-------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------- exact H12.
-------------------------------------------------------------------- exact H13.
-------------------------------------------------------------------- exact H14.
-------------------------------------------------------------------- exact H15.
-------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------- exact H26.
-------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------- exact H42.
-------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------- exact H44.
-------------------------------------------------------------------- exact H45.
-------------------------------------------------------------------- exact H46.
-------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------- exact H49.
-------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------- exact H52.
-------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------- exact H58.
-------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------- exact H62.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- exact H70.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A D A)) as H72.
-------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennessidentity (A) D).
-------------------------------------------------------------------- apply (@H14 H69).
------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
-------------------------------------------------------------------intro H71.
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H72.
-------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))))) as H74.
--------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H76.
---------------------------------------------------------------------- exact H73.
---------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))))) as H78.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H80.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))) as H82.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H84.
-------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))) as H86.
--------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H88.
---------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))) as H90.
----------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* Cut *) (False) as H92.
------------------------------------------------------------------------------ apply (@H14 H69).
------------------------------------------------------------------------------ assert (* Cut *) (False) as H93.
------------------------------------------------------------------------------- apply (@H54 H69).
------------------------------------------------------------------------------- assert (* Cut *) (False) as H94.
-------------------------------------------------------------------------------- apply (@H70 H71).
-------------------------------------------------------------------------------- assert False.
---------------------------------------------------------------------------------exact H94.
--------------------------------------------------------------------------------- contradiction.

----------------------------------------------------------------- assert (A = E \/ (F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))) as H70.
------------------------------------------------------------------ exact H69.
------------------------------------------------------------------ destruct H70 as [H70|H70].
------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H71.
-------------------------------------------------------------------- intro H71.
apply (@H64 H70).
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
---------------------------------------------------------------------intro H72.
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H73.
---------------------------------------------------------------------- exact H34.
---------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))))) as H75.
----------------------------------------------------------------------- exact H38.
----------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H77.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))))) as H79.
------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H81.
-------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))) as H83.
--------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H85.
---------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))) as H87.
----------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H89.
------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))) as H91.
------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* Cut *) (False) as H93.
-------------------------------------------------------------------------------- apply (@H64 H70).
-------------------------------------------------------------------------------- assert (* Cut *) (False) as H94.
--------------------------------------------------------------------------------- apply (@H71 H72).
--------------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------------exact H94.
---------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------- assert (F = E \/ (euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F))) as H71.
-------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------- destruct H71 as [H71|H71].
--------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H72.
---------------------------------------------------------------------- intro H72.
assert (* Cut *) (E = F) as H73.
----------------------------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (E) (F) H71).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E F) as H74.
------------------------------------------------------------------------ right.
right.
left.
exact H73.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E B F) as H75.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H75.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (F) H74).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H76.
--------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)))) as H78.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))) as H80.
----------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)) as H82.
------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------ destruct H82 as [H82 H83].
exact H76.
------------------------------------------------------------------------- assert (* Cut *) (F = F) as H76.
-------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point F (fun E0: euclidean__axioms.Point => (euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__defs.Par E0 B C F) -> ((euclidean__defs.Par E0 F B C) -> ((euclidean__defs.Par E0 B F C) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A D E0 F) -> ((euclidean__axioms.Col F A E0) -> ((euclidean__axioms.Col A E0 D) -> ((euclidean__axioms.BetS E0 m C) -> ((~(A = E0)) -> ((~(euclidean__axioms.BetS A F E0)) -> ((euclidean__axioms.Col A F E0) -> ((~(euclidean__axioms.BetS A E0 F)) -> ((E0 = F) -> ((euclidean__axioms.Col B E0 F) -> ((euclidean__axioms.Col E0 B F) -> (F = F)))))))))))))))))))) with (y := E).
---------------------------------------------------------------------------intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
assert (* Cut *) (F = F) as H94.
---------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------- exact H94.

--------------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------- exact H22.
--------------------------------------------------------------------------- exact H6.
--------------------------------------------------------------------------- exact H8.
--------------------------------------------------------------------------- exact H9.
--------------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C F) as H77.
--------------------------------------------------------------------------- right.
left.
exact H76.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H78.
---------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H78.
----------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H79.
------------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------------- destruct H79 as [x H79].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H80.
-------------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------------- destruct H80 as [x0 H80].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H81.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- destruct H81 as [x1 H81].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [x2 H82].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H83.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H83 as [x3 H83].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H84.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H86.
------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H88.
-------------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H90.
--------------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H92.
---------------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H94.
----------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H96.
------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H98.
------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H100.
-------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H102.
--------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H104.
---------------------------------------------------------------------------------------------- exact H5.
---------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H105.
------------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------------ destruct H105 as [x4 H105].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H106.
------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------- destruct H106 as [x5 H106].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [x6 H107].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H108.
--------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------- destruct H108 as [x7 H108].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H109.
---------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------- destruct H109 as [x8 H109].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H110.
----------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H112.
------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H114.
------------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H116.
-------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H118.
--------------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H120.
---------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H122.
----------------------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H124.
------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H126.
------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H128.
-------------------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H130.
--------------------------------------------------------------------------------------------------------------- exact H22.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H131.
----------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------------- destruct H131 as [x9 H131].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H132.
------------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------------ destruct H132 as [x10 H132].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H133.
------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------- destruct H133 as [x11 H133].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H134.
-------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------- destruct H134 as [x12 H134].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H135.
--------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------- destruct H135 as [x13 H135].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H136.
---------------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H138.
----------------------------------------------------------------------------------------------------------------------- exact H137.
----------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H140.
------------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H142.
------------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H144.
-------------------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H146.
--------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H148.
---------------------------------------------------------------------------------------------------------------------------- exact H147.
---------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H150.
----------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H152.
------------------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H154.
------------------------------------------------------------------------------------------------------------------------------- exact H153.
------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H156.
-------------------------------------------------------------------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H157.
---------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [x14 H157].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H158.
----------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [x15 H158].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------------------------------ destruct H159 as [x16 H159].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H160.
------------------------------------------------------------------------------------------------------------------------------------- exact H159.
------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x17 H160].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H161.
-------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x18 H161].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H164.
---------------------------------------------------------------------------------------------------------------------------------------- exact H163.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H166.
----------------------------------------------------------------------------------------------------------------------------------------- exact H165.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------------------ exact H167.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H180.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H179.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [x19 H183].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H184.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [x20 H184].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H185.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [x21 H185].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [x22 H186].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x23 H187].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H190.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H194.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H200.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H202.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H204.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H206.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H23.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [x24 H209].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [x25 H210].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [x26 H211].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x27 H212].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [x28 H213].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H216.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H218.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H220.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H222.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H228.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H228 H229].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H230.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H232.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
exact H162.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F C) as H79.
----------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H79.
------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H80.
-------------------------------------------------------------------------------- exact __TmpHyp0.
-------------------------------------------------------------------------------- destruct H80 as [x H80].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H81.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- destruct H81 as [x0 H81].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [x1 H82].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H83.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H83 as [x2 H83].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H84.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ destruct H84 as [x3 H84].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H85.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H87.
-------------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H89.
--------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H91.
---------------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H93.
----------------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H97.
------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H99.
-------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H101.
--------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H103.
---------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H105.
----------------------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H106.
------------------------------------------------------------------------------------------------- exact __TmpHyp1.
------------------------------------------------------------------------------------------------- destruct H106 as [x4 H106].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [x5 H107].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H108.
--------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------- destruct H108 as [x6 H108].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H109.
---------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------- destruct H109 as [x7 H109].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H110.
----------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------- destruct H110 as [x8 H110].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H111.
------------------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------------------ destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H113.
------------------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H115.
-------------------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H117.
--------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H119.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H121.
----------------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H123.
------------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H125.
------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H127.
-------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H129.
--------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H131.
---------------------------------------------------------------------------------------------------------------- exact H22.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
----------------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H132.
------------------------------------------------------------------------------------------------------------------ exact __TmpHyp2.
------------------------------------------------------------------------------------------------------------------ destruct H132 as [x9 H132].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H133.
------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------- destruct H133 as [x10 H133].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H134.
-------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------- destruct H134 as [x11 H134].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H135.
--------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------- destruct H135 as [x12 H135].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H136.
---------------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------------- destruct H136 as [x13 H136].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H137.
----------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H139.
------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H141.
------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H143.
-------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H145.
--------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H147.
---------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H149.
----------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H151.
------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H151 H152].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H153.
------------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H155.
-------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H157.
--------------------------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------------- exact H157.
---------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H158.
----------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [x14 H158].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------------------------------ destruct H159 as [x15 H159].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H160.
------------------------------------------------------------------------------------------------------------------------------------- exact H159.
------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x16 H160].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H161.
-------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x17 H161].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x18 H162].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H163.
---------------------------------------------------------------------------------------------------------------------------------------- exact H162.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H165.
----------------------------------------------------------------------------------------------------------------------------------------- exact H164.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------ exact H166.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H169.
------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H171.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H173.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H175.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H177.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H181.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H183.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H184.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [x19 H184].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H185.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [x20 H185].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [x21 H186].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x22 H187].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [x23 H188].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [H207 H208].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [x24 H210].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [x25 H211].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x26 H212].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [x27 H213].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [x28 H214].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H217.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H219.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H221.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H227.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H229.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H231.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H233.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
exact H87.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E B F C) as H80.
------------------------------------------------------------------------------ exists F.
split.
------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.Meet E B F C)) as H81.
------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81.
-------------------------------------------------------------------------------- exact H6.
-------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
--------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
---------------------------------------------------------------------------------- exact __TmpHyp0.
---------------------------------------------------------------------------------- destruct H82 as [x H82].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H83.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H83 as [x0 H83].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H84.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ destruct H84 as [x1 H84].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H85.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H85 as [x2 H85].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H86.
-------------------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------------------- destruct H86 as [x3 H86].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H87.
--------------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H89.
---------------------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col E B x) /\ ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H91.
----------------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col E B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H93.
------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H95.
------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col F C x1) /\ ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H97.
-------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col F C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H99.
--------------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H101.
---------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H103.
----------------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H105.
------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107.
------------------------------------------------------------------------------------------------- exact H5.
------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
-------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H108.
--------------------------------------------------------------------------------------------------- exact __TmpHyp1.
--------------------------------------------------------------------------------------------------- destruct H108 as [x4 H108].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H109.
---------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------- destruct H109 as [x5 H109].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H110.
----------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------- destruct H110 as [x6 H110].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H111.
------------------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------------------ destruct H111 as [x7 H111].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H112.
------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------- destruct H112 as [x8 H112].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H113.
-------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H115.
--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H117.
---------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H119.
----------------------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H121.
------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H123.
------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H125.
-------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H127.
--------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H129.
---------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H131.
----------------------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133.
------------------------------------------------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H134.
-------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
-------------------------------------------------------------------------------------------------------------------- destruct H134 as [x9 H134].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H135.
--------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------- destruct H135 as [x10 H135].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H136.
---------------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------------- destruct H136 as [x11 H136].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H137.
----------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------- destruct H137 as [x12 H137].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H138.
------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------ destruct H138 as [x13 H138].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H139.
------------------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H141.
-------------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col E F x9) /\ ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H143.
--------------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col E F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H145.
---------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H147.
----------------------------------------------------------------------------------------------------------------------------- exact H146.
----------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H149.
------------------------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------------------------ destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H151.
------------------------------------------------------------------------------------------------------------------------------- exact H150.
------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H153.
-------------------------------------------------------------------------------------------------------------------------------- exact H152.
-------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H155.
--------------------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H157.
---------------------------------------------------------------------------------------------------------------------------------- exact H156.
---------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159.
----------------------------------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H160.
------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x14 H160].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H161.
-------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x15 H161].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x16 H162].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H163.
---------------------------------------------------------------------------------------------------------------------------------------- exact H162.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [x17 H163].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H164.
----------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [x18 H164].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col E B x14) /\ ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.Col E B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H171.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col C F x16) /\ ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col C F x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [x19 H186].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x20 H187].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [x21 H188].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [x22 H189].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [x23 H190].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col A D x19) /\ ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.Col A D x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H199.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.Col B C x21) /\ ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H201.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.Col B C x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H203.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H205.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H205 as [H205 H206].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H23.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x24 H212].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [x25 H213].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [x26 H214].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [x27 H215].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [x28 H216].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H225.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.Col C D x26) /\ ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.Col C D x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H229.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H231.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H232.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H235.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
exact H103.
------------------------------------------------------------------------------- apply (@H81 H80).
---------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
-----------------------------------------------------------------------intro H73.
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H74.
------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))))) as H76.
------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H78.
-------------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))))) as H80.
--------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H82.
---------------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))) as H84.
----------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H86.
------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------ destruct H86 as [H86 H87].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))) as H88.
------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H90.
-------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))) as H92.
--------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* Cut *) (False) as H94.
---------------------------------------------------------------------------------- apply (@H72 H73).
---------------------------------------------------------------------------------- assert False.
-----------------------------------------------------------------------------------exact H94.
----------------------------------------------------------------------------------- contradiction.

--------------------------------------------------------------------- assert (euclidean__axioms.BetS F A E \/ (euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)) as H72.
---------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------- destruct H72 as [H72|H72].
----------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H73.
------------------------------------------------------------------------ intro H73.
assert (* Cut *) (euclidean__axioms.BetS F D A) as H74.
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (F) H1).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D A E) as H75.
-------------------------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (F) (D) (A) (E) (H74) H72).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A D A) as H76.
--------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (D) A).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A D E) as H77.
---------------------------------------------------------------------------- exists A.
split.
----------------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A A D) as H78.
----------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (D) A).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D D E) as H79.
------------------------------------------------------------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (D) (A) (D) (E) (A) (D) (H77) H78).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D E E D) as H80.
------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (D) E).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D E D) as H81.
-------------------------------------------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (D) (D) (E) (E) (D) (H79) H80).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A D) as H82.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) D).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D A F) as H83.
---------------------------------------------------------------------------------- exists D.
split.
----------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D D A) as H84.
----------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (A) D).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A A F) as H85.
------------------------------------------------------------------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (A) (D) (A) (F) (D) (A) (H83) H84).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A F F A) as H86.
------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (A) F).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A F A) as H87.
-------------------------------------------------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (D) (A) (A) (F) (F) (A) (H85) H86).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F A F A) as H88.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (F) A).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F A F E) as H89.
---------------------------------------------------------------------------------------- exists A.
split.
----------------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A F E) as H90.
----------------------------------------------------------------------------------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive (D) (A) (F) (A) (F) (E) (H87) H89).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A F E) as H91.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong D A F E) /\ ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E))) as H91.
------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (D) (E) (F) H10).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A F E) /\ ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E))) as H92.
-------------------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E)) as H94.
--------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H92.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Lt F E F E) as H92.
------------------------------------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (D) (A) (F) (E) (F) (E) (H90) H91).
------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt F E F E)) as H93.
-------------------------------------------------------------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (F) (E) (F) (E) H92).
-------------------------------------------------------------------------------------------- apply (@H93 H92).
------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
-------------------------------------------------------------------------intro H74.
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H75.
-------------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))))) as H77.
--------------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H79.
---------------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))))) as H81.
----------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H83.
------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))) as H85.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H87.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))) as H89.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H91.
---------------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))) as H93.
----------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* Cut *) (False) as H95.
------------------------------------------------------------------------------------ apply (@H73 H74).
------------------------------------------------------------------------------------ assert False.
-------------------------------------------------------------------------------------exact H95.
------------------------------------------------------------------------------------- contradiction.

----------------------------------------------------------------------- assert (euclidean__axioms.BetS A F E \/ euclidean__axioms.BetS A E F) as H73.
------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------ destruct H73 as [H73|H73].
------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H74.
-------------------------------------------------------------------------- intro H74.
apply (@H65 H73).
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
---------------------------------------------------------------------------intro H75.
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H76.
---------------------------------------------------------------------------- exact H34.
---------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))))) as H78.
----------------------------------------------------------------------------- exact H38.
----------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H80.
------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))))) as H82.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H84.
-------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))))) as H86.
--------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H88.
---------------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F B)) /\ ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B)))) as H90.
----------------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H92.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B F)) /\ (~(euclidean__axioms.BetS F A B))) as H94.
------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* Cut *) (False) as H96.
-------------------------------------------------------------------------------------- apply (@H65 H73).
-------------------------------------------------------------------------------------- assert (* Cut *) (False) as H97.
--------------------------------------------------------------------------------------- apply (@H74 H75).
--------------------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------------------exact H97.
---------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------- exact H73.
------------------------------------------------------------- exact H68.
Qed.
