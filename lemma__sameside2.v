Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__9__5a.
Require Export lemma__9__5b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray1.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__sameside2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__defs.OS E F A C) -> ((euclidean__axioms.Col A B C) -> ((euclidean__defs.Out B F G) -> (euclidean__defs.OS E G A C))).
Proof.
intro A.
intro B.
intro C.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (Q: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F)))))) as H2.
- exact H.
- assert (exists Q: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F))))))) as H3.
-- exact H2.
-- destruct H3 as [Q H3].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F))))))) as H4.
--- exact H3.
--- destruct H4 as [U H4].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F))))))) as H5.
---- exact H4.
---- destruct H5 as [V H5].
assert (* AndElim *) ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F)))))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS E U Q) /\ ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS F V Q) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol A C F)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.TS F A C Q) as H16.
---------- exists V.
split.
----------- exact H12.
----------- split.
------------ exact H8.
------------ exact H15.
---------- assert (* Cut *) (euclidean__axioms.Col A C B) as H17.
----------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H17.
------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H0).
------------ assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
exact H24.
----------- assert (* Cut *) (~(A = C)) as H18.
------------ intro H18.
assert (* Cut *) (euclidean__axioms.Col A C F) as H19.
------------- left.
exact H18.
------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (F) (H15) H19).
------------ assert (* Cut *) (euclidean__axioms.Col B F G) as H19.
------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (F) (G) H1).
------------- assert (* Cut *) (euclidean__axioms.Col B G F) as H20.
-------------- assert (* Cut *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H20.
--------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (G) H19).
--------------- assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
exact H27.
-------------- assert (* Cut *) (euclidean__axioms.Col A C B) as H21.
--------------- assert (* Cut *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H21.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (F) H20).
---------------- assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)))) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
exact H17.
--------------- assert (* Cut *) (~(~(euclidean__axioms.TS G A C Q))) as H22.
---------------- intro H22.
assert (* Cut *) (~(F = G)) as H23.
----------------- intro H23.
assert (* Cut *) (euclidean__axioms.TS G A C Q) as H24.
------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.OS E F0 A C) -> ((euclidean__defs.Out B F0 G) -> ((euclidean__axioms.BetS F0 V Q) -> ((euclidean__axioms.nCol A C F0) -> ((euclidean__axioms.TS F0 A C Q) -> ((euclidean__axioms.Col B F0 G) -> ((euclidean__axioms.Col B G F0) -> (euclidean__axioms.TS G A C Q))))))))) with (x := F).
-------------------intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
exact H28.

------------------- exact H23.
------------------- exact H.
------------------- exact H1.
------------------- exact H12.
------------------- exact H15.
------------------- exact H16.
------------------- exact H19.
------------------- exact H20.
------------------ apply (@H22 H24).
----------------- assert (* Cut *) (~(B = V)) as H24.
------------------ intro H24.
assert (* Cut *) (euclidean__axioms.BetS F B Q) as H25.
------------------- apply (@eq__ind__r euclidean__axioms.Point V (fun B0: euclidean__axioms.Point => (euclidean__axioms.Col A B0 C) -> ((euclidean__defs.Out B0 F G) -> ((euclidean__axioms.Col A C B0) -> ((euclidean__axioms.Col B0 F G) -> ((euclidean__axioms.Col B0 G F) -> ((euclidean__axioms.Col A C B0) -> (euclidean__axioms.BetS F B0 Q)))))))) with (x := B).
--------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
exact H12.

-------------------- exact H24.
-------------------- exact H0.
-------------------- exact H1.
-------------------- exact H17.
-------------------- exact H19.
-------------------- exact H20.
-------------------- exact H21.
------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as H26.
-------------------- apply (@lemma__ray1.lemma__ray1 (B) (F) (G) H1).
-------------------- assert (* Cut *) (euclidean__axioms.BetS G B Q) as H27.
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as H27.
---------------------- exact H26.
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as __TmpHyp.
----------------------- exact H27.
----------------------- assert (euclidean__axioms.BetS B G F \/ (F = G) \/ (euclidean__axioms.BetS B F G)) as H28.
------------------------ exact __TmpHyp.
------------------------ destruct H28 as [H28|H28].
------------------------- assert (* Cut *) (euclidean__axioms.BetS F G B) as H29.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (G) (F) H28).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS G B Q) as H30.
--------------------------- apply (@lemma__3__6a.lemma__3__6a (F) (G) (B) (Q) (H29) H25).
--------------------------- exact H30.
------------------------- assert (F = G \/ euclidean__axioms.BetS B F G) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29|H29].
--------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G B Q))) as H30.
---------------------------- intro H30.
apply (@H23 H29).
---------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G B Q)).
-----------------------------intro H31.
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS A C E)) /\ ((~(euclidean__axioms.BetS A E C)) /\ (~(euclidean__axioms.BetS C A E))))))) as H32.
------------------------------ exact H14.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq C F) /\ ((~(euclidean__axioms.BetS A C F)) /\ ((~(euclidean__axioms.BetS A F C)) /\ (~(euclidean__axioms.BetS C A F))))))) as H34.
------------------------------- exact H15.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS A C E)) /\ ((~(euclidean__axioms.BetS A E C)) /\ (~(euclidean__axioms.BetS C A E)))))) as H36.
-------------------------------- exact H33.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq C F) /\ ((~(euclidean__axioms.BetS A C F)) /\ ((~(euclidean__axioms.BetS A F C)) /\ (~(euclidean__axioms.BetS C A F)))))) as H38.
--------------------------------- exact H35.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS A C E)) /\ ((~(euclidean__axioms.BetS A E C)) /\ (~(euclidean__axioms.BetS C A E))))) as H40.
---------------------------------- exact H37.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ ((~(euclidean__axioms.BetS A C F)) /\ ((~(euclidean__axioms.BetS A F C)) /\ (~(euclidean__axioms.BetS C A F))))) as H42.
----------------------------------- exact H39.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C E)) /\ ((~(euclidean__axioms.BetS A E C)) /\ (~(euclidean__axioms.BetS C A E)))) as H44.
------------------------------------ exact H41.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C F)) /\ ((~(euclidean__axioms.BetS A F C)) /\ (~(euclidean__axioms.BetS C A F)))) as H46.
------------------------------------- exact H43.
------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((~(euclidean__axioms.BetS A E C)) /\ (~(euclidean__axioms.BetS C A E))) as H48.
-------------------------------------- exact H45.
-------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((~(euclidean__axioms.BetS A F C)) /\ (~(euclidean__axioms.BetS C A F))) as H50.
--------------------------------------- exact H47.
--------------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) (False) as H52.
---------------------------------------- apply (@H23 H29).
---------------------------------------- assert (* Cut *) (False) as H53.
----------------------------------------- apply (@H30 H31).
----------------------------------------- assert False.
------------------------------------------exact H53.
------------------------------------------ contradiction.

--------------------------- assert (* Cut *) (euclidean__axioms.BetS G F B) as H30.
---------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (F) (G) H29).
---------------------------- assert (* Cut *) (euclidean__axioms.BetS G B Q) as H31.
----------------------------- apply (@lemma__3__7a.lemma__3__7a (G) (F) (B) (Q) (H30) H25).
----------------------------- exact H31.
--------------------- assert (* Cut *) (~(euclidean__axioms.Col A C G)) as H28.
---------------------- intro H28.
assert (* Cut *) (euclidean__axioms.Col A C B) as H29.
----------------------- assert (* Cut *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H29.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (G) H28).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
exact H21.
----------------------- assert (* Cut *) (euclidean__axioms.Col C G B) as H30.
------------------------ apply (@euclidean__tactics.not__nCol__Col (C) (G) (B)).
-------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (C) (G) (B) (H30)).
--------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (C) (G) (B) (H28) (H29) H18).


------------------------ assert (* Cut *) (euclidean__axioms.Col G B C) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))))) as H31.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (B) H30).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C)))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C)) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
exact H34.
------------------------- assert (* Cut *) (euclidean__axioms.Col G B F) as H32.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H32.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (F) H20).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
exact H33.
-------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H33.
--------------------------- apply (@lemma__raystrict.lemma__raystrict (B) (F) (G) H1).
--------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H34.
---------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (G) H33).
---------------------------- assert (* Cut *) (euclidean__axioms.Col B C F) as H35.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (C) (F)).
------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (F) (H35)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (B) (C) (F) (H31) (H32) H34).


----------------------------- assert (* Cut *) (~(euclidean__axioms.neq B C)) as H36.
------------------------------ intro H36.
assert (* Cut *) (euclidean__axioms.Col B C A) as H37.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H37.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H29).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H45.
------------------------------- assert (* Cut *) (euclidean__axioms.Col C F A) as H38.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (F) (A)).
---------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (C) (F) (A) (H38)).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (F) (A) (H35) (H37) H36).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col A C F) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (A) H38).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H44.
--------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (F) (H15) H39).
------------------------------ assert (* Cut *) (euclidean__axioms.Col A B G) as H37.
------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun X: euclidean__axioms.Point => euclidean__axioms.Col A X G)) with (x := B).
-------------------------------- exact H28.
--------------------------------apply (@euclidean__tactics.NNPP (B = C) H36).

------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H38.
-------------------------------- assert (* Cut *) (B = C) as H38.
--------------------------------- apply (@euclidean__tactics.NNPP (B = C) H36).
--------------------------------- intro H39.
assert (* Cut *) (A = C) as Heq.
---------------------------------- apply (@logic.eq__trans (Point) (A) (B) (C) (H39) H38).
---------------------------------- assert False.
-----------------------------------apply (@H18 Heq).
----------------------------------- contradiction.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H47.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A F) as H40.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (F)).
-----------------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (F) (H40)).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (B) (A) (F) (H39) (H32) H34).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H41.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H41.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (F) H40).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
exact H42.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col A C F) as H42.
------------------------------------ apply (@eq__ind euclidean__axioms.Point B (fun X: euclidean__axioms.Point => euclidean__axioms.Col A X F)) with (y := C).
------------------------------------- exact H41.
-------------------------------------apply (@euclidean__tactics.NNPP (B = C) H36).

------------------------------------ apply (@euclidean__tactics.Col__nCol__False (A) (C) (F) (H15) H42).
---------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H29.
----------------------- exists B.
split.
------------------------ exact H27.
------------------------ split.
------------------------- exact H21.
------------------------- apply (@euclidean__tactics.nCol__notCol (A) (C) (G) H28).
----------------------- apply (@H22 H29).
------------------ assert (* Cut *) (~(euclidean__axioms.Col Q F B)) as H25.
------------------- intro H25.
assert (* Cut *) (euclidean__axioms.Col F V Q) as H26.
-------------------- right.
right.
right.
right.
left.
exact H12.
-------------------- assert (* Cut *) (euclidean__axioms.Col Q F V) as H27.
--------------------- assert (* Cut *) ((euclidean__axioms.Col V F Q) /\ ((euclidean__axioms.Col V Q F) /\ ((euclidean__axioms.Col Q F V) /\ ((euclidean__axioms.Col F Q V) /\ (euclidean__axioms.Col Q V F))))) as H27.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (V) (Q) H26).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col V F Q) /\ ((euclidean__axioms.Col V Q F) /\ ((euclidean__axioms.Col Q F V) /\ ((euclidean__axioms.Col F Q V) /\ (euclidean__axioms.Col Q V F))))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col V Q F) /\ ((euclidean__axioms.Col Q F V) /\ ((euclidean__axioms.Col F Q V) /\ (euclidean__axioms.Col Q V F)))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col Q F V) /\ ((euclidean__axioms.Col F Q V) /\ (euclidean__axioms.Col Q V F))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col F Q V) /\ (euclidean__axioms.Col Q V F)) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
exact H32.
--------------------- assert (* Cut *) (euclidean__axioms.neq F Q) as H28.
---------------------- assert (* Cut *) ((euclidean__axioms.neq V Q) /\ ((euclidean__axioms.neq F V) /\ (euclidean__axioms.neq F Q))) as H28.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (V) (Q) H12).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq V Q) /\ ((euclidean__axioms.neq F V) /\ (euclidean__axioms.neq F Q))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq F V) /\ (euclidean__axioms.neq F Q)) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
exact H32.
---------------------- assert (* Cut *) (euclidean__axioms.neq Q F) as H29.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (Q) H28).
----------------------- assert (* Cut *) (euclidean__axioms.Col F B V) as H30.
------------------------ apply (@euclidean__tactics.not__nCol__Col (F) (B) (V)).
-------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (F) (B) (V) (H30)).
--------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (F) (B) (V) (H25) (H27) H29).


------------------------ assert (* Cut *) (euclidean__axioms.Col C B V) as H31.
------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (V)).
--------------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (V) (H31)).
---------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (C) (B) (V) (H21) (H8) H18).


------------------------- assert (* Cut *) (euclidean__axioms.Col B V F) as H32.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col B F V) /\ ((euclidean__axioms.Col B V F) /\ ((euclidean__axioms.Col V F B) /\ ((euclidean__axioms.Col F V B) /\ (euclidean__axioms.Col V B F))))) as H32.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (B) (V) H30).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col B F V) /\ ((euclidean__axioms.Col B V F) /\ ((euclidean__axioms.Col V F B) /\ ((euclidean__axioms.Col F V B) /\ (euclidean__axioms.Col V B F))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B V F) /\ ((euclidean__axioms.Col V F B) /\ ((euclidean__axioms.Col F V B) /\ (euclidean__axioms.Col V B F)))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col V F B) /\ ((euclidean__axioms.Col F V B) /\ (euclidean__axioms.Col V B F))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col F V B) /\ (euclidean__axioms.Col V B F)) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
exact H35.
-------------------------- assert (* Cut *) (euclidean__axioms.Col B V C) as H33.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.Col B V C) /\ ((euclidean__axioms.Col V C B) /\ ((euclidean__axioms.Col C V B) /\ (euclidean__axioms.Col V B C))))) as H33.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (V) H31).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.Col B V C) /\ ((euclidean__axioms.Col V C B) /\ ((euclidean__axioms.Col C V B) /\ (euclidean__axioms.Col V B C))))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col B V C) /\ ((euclidean__axioms.Col V C B) /\ ((euclidean__axioms.Col C V B) /\ (euclidean__axioms.Col V B C)))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col V C B) /\ ((euclidean__axioms.Col C V B) /\ (euclidean__axioms.Col V B C))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C V B) /\ (euclidean__axioms.Col V B C)) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
exact H36.
--------------------------- assert (* Cut *) (euclidean__axioms.Col V F C) as H34.
---------------------------- apply (@euclidean__tactics.not__nCol__Col (V) (F) (C)).
-----------------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False (V) (F) (C) (H34)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (V) (F) (C) (H32) (H33) H24).


---------------------------- assert (* Cut *) (euclidean__axioms.Col V C F) as H35.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col F V C) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.Col C V F) /\ ((euclidean__axioms.Col V C F) /\ (euclidean__axioms.Col C F V))))) as H35.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (V) (F) (C) H34).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F V C) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.Col C V F) /\ ((euclidean__axioms.Col V C F) /\ (euclidean__axioms.Col C F V))))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.Col C V F) /\ ((euclidean__axioms.Col V C F) /\ (euclidean__axioms.Col C F V)))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C V F) /\ ((euclidean__axioms.Col V C F) /\ (euclidean__axioms.Col C F V))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col V C F) /\ (euclidean__axioms.Col C F V)) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
exact H42.
----------------------------- assert (* Cut *) (euclidean__axioms.Col V C A) as H36.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.Col C V A) /\ ((euclidean__axioms.Col V A C) /\ ((euclidean__axioms.Col A V C) /\ (euclidean__axioms.Col V C A))))) as H36.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (V) H8).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.Col C V A) /\ ((euclidean__axioms.Col V A C) /\ ((euclidean__axioms.Col A V C) /\ (euclidean__axioms.Col V C A))))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C V A) /\ ((euclidean__axioms.Col V A C) /\ ((euclidean__axioms.Col A V C) /\ (euclidean__axioms.Col V C A)))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col V A C) /\ ((euclidean__axioms.Col A V C) /\ (euclidean__axioms.Col V C A))) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col A V C) /\ (euclidean__axioms.Col V C A)) as H43.
----------------------------------- exact H42.
----------------------------------- destruct H43 as [H43 H44].
exact H44.
------------------------------ assert (* Cut *) (~(euclidean__axioms.neq V C)) as H37.
------------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.Col C F A) as H38.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (F) (A)).
---------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (C) (F) (A) (H38)).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 (V) (C) (F) (A) (H35) (H36) H37).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col A C F) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (A) H38).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C A F) /\ (euclidean__axioms.Col A F C)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H44.
--------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (F) (H15) H39).
------------------------------- assert (* Cut *) (euclidean__axioms.neq A V) as H38.
-------------------------------- assert (* Cut *) (V = C) as H38.
--------------------------------- apply (@euclidean__tactics.NNPP (V = C) H37).
--------------------------------- intro H39.
assert (* Cut *) (A = C) as Heq.
---------------------------------- apply (@logic.eq__trans (Point) (A) (V) (C) (H39) H38).
---------------------------------- assert False.
-----------------------------------apply (@H18 Heq).
----------------------------------- contradiction.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq V A) as H39.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (V) H38).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H40.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H40.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H21).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
exact H41.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col C A V) as H41.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col C V A) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V A C) /\ (euclidean__axioms.Col A C V))))) as H41.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (V) (C) (A) H36).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C V A) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V A C) /\ (euclidean__axioms.Col A C V))))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V A C) /\ (euclidean__axioms.Col A C V)))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V A C) /\ (euclidean__axioms.Col A C V))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col V A C) /\ (euclidean__axioms.Col A C V)) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
exact H44.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq C A) as H42.
------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H18).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B V) as H43.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (V)).
--------------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (V) (H43)).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (A) (B) (V) (H40) (H41) H42).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col B V A) as H44.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.Col B V A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A V B) /\ (euclidean__axioms.Col V B A))))) as H44.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (V) H43).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.Col B V A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A V B) /\ (euclidean__axioms.Col V B A))))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col B V A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A V B) /\ (euclidean__axioms.Col V B A)))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A V B) /\ (euclidean__axioms.Col V B A))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A V B) /\ (euclidean__axioms.Col V B A)) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
exact H47.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col V F A) as H45.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col (V) (F) (A)).
----------------------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False (V) (F) (A) (H45)).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (V) (F) (A) (H32) (H44) H24).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col V A F) as H46.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F V A) /\ ((euclidean__axioms.Col F A V) /\ ((euclidean__axioms.Col A V F) /\ ((euclidean__axioms.Col V A F) /\ (euclidean__axioms.Col A F V))))) as H46.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (V) (F) (A) H45).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F V A) /\ ((euclidean__axioms.Col F A V) /\ ((euclidean__axioms.Col A V F) /\ ((euclidean__axioms.Col V A F) /\ (euclidean__axioms.Col A F V))))) as H47.
------------------------------------------ exact H46.
------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col F A V) /\ ((euclidean__axioms.Col A V F) /\ ((euclidean__axioms.Col V A F) /\ (euclidean__axioms.Col A F V)))) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A V F) /\ ((euclidean__axioms.Col V A F) /\ (euclidean__axioms.Col A F V))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col V A F) /\ (euclidean__axioms.Col A F V)) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
exact H53.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col V A C) as H47.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V C A) /\ ((euclidean__axioms.Col C V A) /\ (euclidean__axioms.Col V A C))))) as H47.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (V) H41).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V C A) /\ ((euclidean__axioms.Col C V A) /\ (euclidean__axioms.Col V A C))))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col A V C) /\ ((euclidean__axioms.Col V C A) /\ ((euclidean__axioms.Col C V A) /\ (euclidean__axioms.Col V A C)))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col V C A) /\ ((euclidean__axioms.Col C V A) /\ (euclidean__axioms.Col V A C))) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col C V A) /\ (euclidean__axioms.Col V A C)) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
exact H55.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F C) as H48.
------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (F) (C)).
-------------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False (A) (F) (C) (H48)).
--------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (V) (A) (F) (C) (H46) (H47) H39).


------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A C F) as H49.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col C A F) /\ ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A))))) as H49.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (C) H48).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col C A F) /\ ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A))))) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col C A F) /\ ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A)))) as H52.
---------------------------------------------- exact H51.
---------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col C A F) /\ ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A))) as H54.
----------------------------------------------- exact H53.
----------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A)) as H56.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H56 as [H56 H57].
exact H56.
------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (F) (H15) H49).
------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as H26.
-------------------- apply (@lemma__ray1.lemma__ray1 (B) (F) (G) H1).
-------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H27.
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as H27.
---------------------- exact H26.
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B G F) \/ ((F = G) \/ (euclidean__axioms.BetS B F G))) as __TmpHyp.
----------------------- exact H27.
----------------------- assert (euclidean__axioms.BetS B G F \/ (F = G) \/ (euclidean__axioms.BetS B F G)) as H28.
------------------------ exact __TmpHyp.
------------------------ destruct H28 as [H28|H28].
------------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H29.
-------------------------- apply (@lemma__9__5b.lemma__9__5b (A) (C) (Q) (F) (G) (B) (H16) (H28)).
---------------------------apply (@euclidean__tactics.nCol__notCol (Q) (F) (B) H25).

--------------------------- exact H21.
-------------------------- exact H29.
------------------------- assert (F = G \/ euclidean__axioms.BetS B F G) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29|H29].
--------------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H30.
---------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.OS E F0 A C) -> ((euclidean__defs.Out B F0 G) -> ((euclidean__axioms.BetS F0 V Q) -> ((euclidean__axioms.nCol A C F0) -> ((euclidean__axioms.TS F0 A C Q) -> ((euclidean__axioms.Col B F0 G) -> ((euclidean__axioms.Col B G F0) -> ((~(F0 = G)) -> ((~(euclidean__axioms.Col Q F0 B)) -> (euclidean__axioms.TS G A C Q))))))))))) with (x := F).
-----------------------------intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
exact H34.

----------------------------- exact H29.
----------------------------- exact H.
----------------------------- exact H1.
----------------------------- exact H12.
----------------------------- exact H15.
----------------------------- exact H16.
----------------------------- exact H19.
----------------------------- exact H20.
----------------------------- exact H23.
----------------------------- exact H25.
---------------------------- exact H30.
--------------------------- assert (* Cut *) (~(euclidean__axioms.Col B G Q)) as H30.
---------------------------- intro H30.
assert (* Cut *) (euclidean__axioms.Col G B F) as H31.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H31.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (F) H20).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H32.
------------------------------- exact H31.
------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)))) as H34.
-------------------------------- exact H33.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
exact H32.
----------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H32.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B G))) as H32.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (F) (G) H29).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B G))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B G)) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
exact H36.
------------------------------ assert (* Cut *) (euclidean__axioms.neq G B) as H33.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (G) H32).
------------------------------- assert (* Cut *) (euclidean__axioms.Col G B Q) as H34.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col G B Q) /\ ((euclidean__axioms.Col G Q B) /\ ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B Q G) /\ (euclidean__axioms.Col Q G B))))) as H34.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (Q) H30).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G B Q) /\ ((euclidean__axioms.Col G Q B) /\ ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B Q G) /\ (euclidean__axioms.Col Q G B))))) as H35.
---------------------------------- exact H34.
---------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col G Q B) /\ ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B Q G) /\ (euclidean__axioms.Col Q G B)))) as H37.
----------------------------------- exact H36.
----------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col Q B G) /\ ((euclidean__axioms.Col B Q G) /\ (euclidean__axioms.Col Q G B))) as H39.
------------------------------------ exact H38.
------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B Q G) /\ (euclidean__axioms.Col Q G B)) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
exact H35.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B F Q) as H35.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (Q)).
----------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (Q) (H35)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (B) (F) (Q) (H31) (H34) H33).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col Q F B) as H36.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col F Q B) /\ ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col B Q F) /\ (euclidean__axioms.Col Q F B))))) as H36.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (Q) H35).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col F Q B) /\ ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col B Q F) /\ (euclidean__axioms.Col Q F B))))) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col F Q B) /\ ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col B Q F) /\ (euclidean__axioms.Col Q F B)))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col B Q F) /\ (euclidean__axioms.Col Q F B))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col B Q F) /\ (euclidean__axioms.Col Q F B)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
exact H44.
---------------------------------- apply (@H25 H36).
---------------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H31.
----------------------------- apply (@lemma__9__5a.lemma__9__5a (A) (C) (Q) (F) (G) (B) (H16) (H29)).
------------------------------apply (@euclidean__tactics.nCol__notCol (B) (G) (Q) H30).

------------------------------ exact H21.
----------------------------- exact H31.
--------------------- apply (@H22 H27).
---------------- assert (* Cut *) (exists (H23: euclidean__axioms.Point), (euclidean__axioms.BetS G H23 Q) /\ ((euclidean__axioms.Col A C H23) /\ (euclidean__axioms.nCol A C G))) as H23.
----------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C G))) as H23.
------------------ apply (@euclidean__tactics.NNPP (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C G))) H22).
------------------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C G))) as H24.
------------------- exact H23.
------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C G))) as __TmpHyp.
-------------------- exact H24.
-------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS G X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C G)))) as H25.
--------------------- exact __TmpHyp.
--------------------- destruct H25 as [x H25].
assert (* AndElim *) ((euclidean__axioms.BetS G x Q) /\ ((euclidean__axioms.Col A C x) /\ (euclidean__axioms.nCol A C G))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col A C x) /\ (euclidean__axioms.nCol A C G)) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS F X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C F))) as H30.
------------------------ exact H16.
------------------------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS F X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C F))) as __TmpHyp0.
------------------------- exact H30.
------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS F X Q) /\ ((euclidean__axioms.Col A C X) /\ (euclidean__axioms.nCol A C F)))) as H31.
-------------------------- exact __TmpHyp0.
-------------------------- destruct H31 as [x0 H31].
assert (* AndElim *) ((euclidean__axioms.BetS F x0 Q) /\ ((euclidean__axioms.Col A C x0) /\ (euclidean__axioms.nCol A C F))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A C x0) /\ (euclidean__axioms.nCol A C F)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exists x.
split.
----------------------------- exact H26.
----------------------------- split.
------------------------------ exact H28.
------------------------------ exact H29.
----------------- assert (exists H24: euclidean__axioms.Point, ((euclidean__axioms.BetS G H24 Q) /\ ((euclidean__axioms.Col A C H24) /\ (euclidean__axioms.nCol A C G)))) as H25.
------------------ exact H23.
------------------ destruct H25 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS G H24 Q) /\ ((euclidean__axioms.Col A C H24) /\ (euclidean__axioms.nCol A C G))) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col A C H24) /\ (euclidean__axioms.nCol A C G)) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* Cut *) (euclidean__defs.OS E G A C) as H30.
--------------------- assert (* Cut *) (euclidean__axioms.TS G A C Q) as H30.
---------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS G A C Q) H22).
---------------------- exists Q.
exists U.
exists H24.
split.
----------------------- exact H6.
----------------------- split.
------------------------ exact H28.
------------------------ split.
------------------------- exact H10.
------------------------- split.
-------------------------- exact H26.
-------------------------- split.
--------------------------- exact H14.
--------------------------- exact H29.
--------------------- exact H30.
Qed.
