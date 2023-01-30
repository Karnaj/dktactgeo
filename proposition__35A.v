Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__35helper.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__EFreflexive.
Require Export lemma__ETreflexive.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGrotate.
Require Export lemma__PGsymmetric.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsmeet.
Require Export lemma__differenceofparts.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__samesidesymmetric.
Require Export lemma__trapezoiddiagonals.
Require Export logic.
Require Export proposition__04.
Require Export proposition__29C.
Require Export proposition__34.
Definition proposition__35A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E B C F) -> ((euclidean__axioms.BetS A D F) -> ((euclidean__axioms.Col A E F) -> (euclidean__axioms.EF A B C D E B C F)))).
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
- assert (* Cut *) (euclidean__defs.Par A B D C) as H4.
-- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H4.
--- exact H3.
--- destruct H4 as [H4 H5].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H6.
---- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H4).
---- assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
exact H9.
-- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H5.
--- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H5.
---- exact H3.
---- destruct H5 as [H5 H6].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H7.
----- apply (@proposition__34.proposition__34 (A) (D) (B) (C) H).
----- assert (* AndElim *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
exact H8.
--- assert (* Cut *) (euclidean__axioms.Cong E F B C) as H6.
---- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H6.
----- exact H3.
----- destruct H6 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H8.
------ apply (@proposition__34.proposition__34 (E) (F) (B) (C) H0).
------ assert (* AndElim *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B)))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B)) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
exact H9.
---- assert (* Cut *) (euclidean__axioms.Cong B C E F) as H7.
----- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H7.
------ exact H3.
------ destruct H7 as [H7 H8].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (E) (F) (C) H6).
----- assert (* Cut *) (euclidean__axioms.Cong A D E F) as H8.
------ assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H8.
------- exact H3.
------- destruct H8 as [H8 H9].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (D) (B) (C) (E) (F) (H5) H7).
------ assert (* Cut *) (euclidean__axioms.Cong E F F E) as H9.
------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H9.
-------- exact H3.
-------- destruct H9 as [H9 H10].
apply (@euclidean__axioms.cn__equalityreverse (E) F).
------- assert (* Cut *) (euclidean__axioms.Cong A D F E) as H10.
-------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10.
--------- exact H3.
--------- destruct H10 as [H10 H11].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (D) (E) (F) (F) (E) (H8) H9).
-------- assert (* Cut *) (euclidean__axioms.Cong A D A D) as H11.
--------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
---------- exact H3.
---------- destruct H11 as [H11 H12].
apply (@euclidean__axioms.cn__congruencereflexive (A) D).
--------- assert (* Cut *) (euclidean__defs.Lt A D A F) as H12.
---------- exists D.
split.
----------- exact H1.
----------- exact H11.
---------- assert (* Cut *) (euclidean__defs.Lt F E A F) as H13.
----------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H13.
------------ exact H3.
------------ destruct H13 as [H13 H14].
apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (A) (D) (A) (F) (F) (E) (H12) H10).
----------- assert (* Cut *) (euclidean__axioms.Cong A F F A) as H14.
------------ assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
------------- exact H3.
------------- destruct H14 as [H14 H15].
apply (@euclidean__axioms.cn__equalityreverse (A) F).
------------ assert (* Cut *) (euclidean__defs.Lt F E F A) as H15.
------------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
-------------- exact H3.
-------------- destruct H15 as [H15 H16].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (F) (E) (A) (F) (F) (A) (H13) H14).
------------- assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS F e A) /\ (euclidean__axioms.Cong F e F E)) as H16.
-------------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16.
--------------- exact H3.
--------------- destruct H16 as [H16 H17].
exact H15.
-------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS F e A) /\ (euclidean__axioms.Cong F e F E))) as H17.
--------------- exact H16.
--------------- destruct H17 as [e H17].
assert (* AndElim *) ((euclidean__axioms.BetS F e A) /\ (euclidean__axioms.Cong F e F E)) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H20.
----------------- exact H3.
----------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.neq F A) as H22.
------------------ assert (* Cut *) ((euclidean__axioms.neq e A) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F A))) as H22.
------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (e) (A) H18).
------------------- assert (* AndElim *) ((euclidean__axioms.neq e A) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F A))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F A)) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
exact H26.
------------------ assert (* Cut *) (euclidean__defs.Out F A e) as H23.
------------------- apply (@lemma__ray4.lemma__ray4 (F) (A) (e)).
--------------------left.
exact H18.

-------------------- exact H22.
------------------- assert (* Cut *) (euclidean__axioms.BetS A E F) as H24.
-------------------- apply (@lemma__35helper.lemma__35helper (A) (B) (C) (D) (E) (F) (H) (H0) (H1) H2).
-------------------- assert (* Cut *) (euclidean__axioms.BetS F E A) as H25.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (F) H24).
--------------------- assert (* Cut *) (euclidean__defs.Out F A E) as H26.
---------------------- apply (@lemma__ray4.lemma__ray4 (F) (A) (E)).
-----------------------left.
exact H25.

----------------------- exact H22.
---------------------- assert (* Cut *) (e = E) as H27.
----------------------- apply (@lemma__layoffunique.lemma__layoffunique (F) (A) (e) (E) (H23) (H26) H19).
----------------------- assert (* Cut *) (euclidean__axioms.BetS F E A) as H28.
------------------------ apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (euclidean__axioms.BetS F E A))))) with (x := e).
-------------------------intro H28.
intro H29.
intro H30.
exact H25.

------------------------- exact H27.
------------------------- exact H18.
------------------------- exact H19.
------------------------- exact H23.
------------------------ assert (* Cut *) (euclidean__axioms.BetS A E F) as H29.
------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (euclidean__axioms.BetS A E F))))) with (x := e).
--------------------------intro H29.
intro H30.
intro H31.
exact H24.

-------------------------- exact H27.
-------------------------- exact H18.
-------------------------- exact H19.
-------------------------- exact H23.
------------------------- assert (* Cut *) (euclidean__defs.Par D C A B) as H30.
-------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (D) (C) H4).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS F D A) as H31.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (F) H1).
--------------------------- assert (* Cut *) (euclidean__defs.TP A D B C) as H32.
---------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (A) (D) (B) (C) H21).
---------------------------- assert (* Cut *) (euclidean__defs.OS B C A D) as H33.
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__defs.Meet A D B C)) /\ (euclidean__defs.OS B C A D)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__defs.Meet A D B C)) /\ (euclidean__defs.OS B C A D))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ (euclidean__defs.OS B C A D)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H38.
----------------------------- assert (* Cut *) (euclidean__defs.OS C B D A) as H34.
------------------------------ assert (* Cut *) ((euclidean__defs.OS C B A D) /\ ((euclidean__defs.OS B C D A) /\ (euclidean__defs.OS C B D A))) as H34.
------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (D) (B) (C) H33).
------------------------------- assert (* AndElim *) ((euclidean__defs.OS C B A D) /\ ((euclidean__defs.OS B C D A) /\ (euclidean__defs.OS C B D A))) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.OS B C D A) /\ (euclidean__defs.OS C B D A)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
exact H38.
------------------------------ assert (* Cut *) (euclidean__defs.CongA F D C D A B) as H35.
------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H35: euclidean__axioms.Point), (euclidean__defs.Par G B0 H35 D0) -> ((euclidean__defs.OS B0 D0 G H35) -> ((euclidean__axioms.BetS E0 G H35) -> (euclidean__defs.CongA E0 G B0 G H35 D0)))) as H35.
-------------------------------- intro B0.
intro D0.
intro E0.
intro G.
intro H35.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G B0 G H35 D0) /\ (euclidean__defs.RT B0 G H35 G H35 D0)) as __2.
--------------------------------- apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G) (H35) (__) (__0) __1).
--------------------------------- destruct __2 as [__2 __3].
exact __2.
-------------------------------- apply (@H35 (C) (B) (F) (D) (A) (H30) (H34) H31).
------------------------------- assert (* Cut *) (D = D) as H36.
-------------------------------- apply (@logic.eq__refl (Point) D).
-------------------------------- assert (* Cut *) (C = C) as H37.
--------------------------------- apply (@logic.eq__refl (Point) C).
--------------------------------- assert (* Cut *) (B = B) as H38.
---------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------- assert (* Cut *) (A = A) as H39.
----------------------------------- apply (@logic.eq__refl (Point) A).
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D C) as H40.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H40.
------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (D) (C) H4).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C))) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
exact H43.
------------------------------------ assert (* Cut *) (~(A = D)) as H41.
------------------------------------- intro H41.
assert (* Cut *) (euclidean__axioms.Col A D C) as H42.
-------------------------------------- left.
exact H41.
-------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (D) (C) (H40) H42).
------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H42.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq F D) /\ (euclidean__axioms.neq F A))) as H42.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (D) (A) H31).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq F D) /\ (euclidean__axioms.neq F A))) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ (euclidean__axioms.neq F A)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
exact H41.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H43.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H43.
---------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (D) (C) H4).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
exact H49.
--------------------------------------- assert (* Cut *) (~(A = B)) as H44.
---------------------------------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col A B C) as H45.
----------------------------------------- left.
exact H44.
----------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H43) H45).
---------------------------------------- assert (* Cut *) (euclidean__defs.Out A B B) as H45.
----------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (B) (B)).
------------------------------------------right.
left.
exact H38.

------------------------------------------ exact H44.
----------------------------------------- assert (* Cut *) (~(~((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))))) as H46.
------------------------------------------ intro H46.
assert (* Cut *) (D = E) as H47.
------------------------------------------- apply (@euclidean__axioms.axiom__connectivity (A) (D) (E) (F) (H1) (H29)).
--------------------------------------------intro H47.
apply (@H46).
---------------------------------------------left.
exact H47.


--------------------------------------------intro H47.
apply (@H46).
---------------------------------------------right.
left.
exact H47.


------------------------------------------- apply (@H46).
--------------------------------------------right.
right.
exact H47.

------------------------------------------ assert (* Cut *) (euclidean__defs.Out A D E) as H47.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H47.
-------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E)))).
---------------------------------------------intro H47.
assert (* Cut *) (False) as H48.
---------------------------------------------- apply (@H46 H47).
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) -> False) as H49.
----------------------------------------------- intro H49.
apply (@H47).
------------------------------------------------left.
exact H49.

----------------------------------------------- assert (* Cut *) (((euclidean__axioms.BetS A E D) \/ (D = E)) -> False) as H50.
------------------------------------------------ intro H50.
apply (@H47).
-------------------------------------------------right.
exact H50.

------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A E D) -> False) as H51.
------------------------------------------------- intro H51.
apply (@H50).
--------------------------------------------------left.
exact H51.

------------------------------------------------- assert (* Cut *) ((D = E) -> False) as H52.
-------------------------------------------------- intro H52.
apply (@H50).
---------------------------------------------------right.
exact H52.

-------------------------------------------------- assert False.
---------------------------------------------------exact H48.
--------------------------------------------------- contradiction.

-------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as __TmpHyp.
---------------------------------------------- exact H48.
---------------------------------------------- assert (euclidean__axioms.BetS A D E \/ (euclidean__axioms.BetS A E D) \/ (D = E)) as H49.
----------------------------------------------- exact __TmpHyp.
----------------------------------------------- destruct H49 as [H49|H49].
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out A D E) as H50.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H50.
-------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (D) (E)).
---------------------------------------------------right.
right.
exact H49.

--------------------------------------------------- exact H42.
------------------------------------------------- exact H50.
------------------------------------------------ assert (euclidean__axioms.BetS A E D \/ D = E) as H50.
------------------------------------------------- exact H49.
------------------------------------------------- destruct H50 as [H50|H50].
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A D E) as H51.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H51.
---------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (D) (E)).
-----------------------------------------------------left.
exact H50.

----------------------------------------------------- exact H42.
--------------------------------------------------- exact H51.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A D D) as H51.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H51.
---------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (D) (D)).
-----------------------------------------------------right.
left.
exact H36.

----------------------------------------------------- exact H42.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A D E) as H52.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H52.
----------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 D0) -> (euclidean__defs.Out A D0 E)))))))))))))))))))))))) with (x := D).
------------------------------------------------------intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__defs.Out A E0 E0) -> (euclidean__defs.Out A E0 E0))))))))))))))))))))))))))))))))))))) with (y := E).
-------------------------------------------------------intro H75.
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
assert (* Cut *) (e = e) as H110.
-------------------------------------------------------- exact H98.
-------------------------------------------------------- exact H109.

------------------------------------------------------- exact H27.
------------------------------------------------------- exact H53.
------------------------------------------------------- exact H0.
------------------------------------------------------- exact H54.
------------------------------------------------------- exact H2.
------------------------------------------------------- exact H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- exact H56.
------------------------------------------------------- exact H55.
------------------------------------------------------- exact H6.
------------------------------------------------------- exact H7.
------------------------------------------------------- exact H59.
------------------------------------------------------- exact H9.
------------------------------------------------------- exact H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- exact H60.
------------------------------------------------------- exact H13.
------------------------------------------------------- exact H15.
------------------------------------------------------- exact H19.
------------------------------------------------------- exact H24.
------------------------------------------------------- exact H25.
------------------------------------------------------- exact H26.
------------------------------------------------------- exact H28.
------------------------------------------------------- exact H29.
------------------------------------------------------- exact H69.
------------------------------------------------------- exact H68.
------------------------------------------------------- exact H67.
------------------------------------------------------- exact H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- exact H72.
------------------------------------------------------- exact H71.
------------------------------------------------------- exact H70.
------------------------------------------------------- exact H73.
------------------------------------------------------- exact H74.

------------------------------------------------------ exact H50.
------------------------------------------------------ exact H.
------------------------------------------------------ exact H1.
------------------------------------------------------ exact H20.
------------------------------------------------------ exact H21.
------------------------------------------------------ exact H4.
------------------------------------------------------ exact H5.
------------------------------------------------------ exact H8.
------------------------------------------------------ exact H10.
------------------------------------------------------ exact H11.
------------------------------------------------------ exact H12.
------------------------------------------------------ exact H30.
------------------------------------------------------ exact H31.
------------------------------------------------------ exact H32.
------------------------------------------------------ exact H33.
------------------------------------------------------ exact H34.
------------------------------------------------------ exact H35.
------------------------------------------------------ exact H36.
------------------------------------------------------ exact H40.
------------------------------------------------------ exact H41.
------------------------------------------------------ exact H42.
------------------------------------------------------ exact H52.
------------------------------------------------------ exact H51.
---------------------------------------------------- exact H52.
------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H48.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H48.
--------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H21).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H51.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
exact H49.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H49.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H49.
---------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (D) (B) H48).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H50.
----------------------------------------------- exact H49.
----------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A)))) as H52.
------------------------------------------------ exact H51.
------------------------------------------------ destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A)) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
exact H50.
--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B D A B) as H50.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H50.
----------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (D) (A) (B) H49).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B E A B) as H51.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H51.
------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (A) (B) (D) (A) (B) (E) (B) (H50) (H47) H45).
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F D C E A B) as H52.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H52.
------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (D) (C) (D) (A) (B) (E) (A) (B) (H35) H51).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A B D C) as H53.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H53.
-------------------------------------------------- apply (@proposition__34.proposition__34 (A) (D) (B) (C) H).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)))) as H56.
---------------------------------------------------- exact H55.
---------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
exact H56.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D E E D) as H54.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H54.
--------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (D) E).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E D F) as H55.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H55.
---------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E)))).
-----------------------------------------------------intro H55.
assert (* Cut *) (False) as H56.
------------------------------------------------------ apply (@H46 H55).
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) -> False) as H57.
------------------------------------------------------- intro H57.
apply (@H55).
--------------------------------------------------------left.
exact H57.

------------------------------------------------------- assert (* Cut *) (((euclidean__axioms.BetS A E D) \/ (D = E)) -> False) as H58.
-------------------------------------------------------- intro H58.
apply (@H55).
---------------------------------------------------------right.
exact H58.

-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A E D) -> False) as H59.
--------------------------------------------------------- intro H59.
apply (@H58).
----------------------------------------------------------left.
exact H59.

--------------------------------------------------------- assert (* Cut *) ((D = E) -> False) as H60.
---------------------------------------------------------- intro H60.
apply (@H58).
-----------------------------------------------------------right.
exact H60.

---------------------------------------------------------- assert False.
-----------------------------------------------------------exact H56.
----------------------------------------------------------- contradiction.

---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H56.
----------------------------------------------------- exact H55.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as __TmpHyp.
------------------------------------------------------ exact H56.
------------------------------------------------------ assert (euclidean__axioms.BetS A D E \/ (euclidean__axioms.BetS A E D) \/ (D = E)) as H57.
------------------------------------------------------- exact __TmpHyp.
------------------------------------------------------- destruct H57 as [H57|H57].
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D E F) as H58.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H58.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (A) (D) (E) (F) (H57) H29).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E D) as H59.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H59.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (E) (F) H58).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E F D) as H60.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H60.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------ apply (@euclidean__axioms.cn__sumofparts (A) (D) (E) (F) (E) (D) (H10) (H54) (H57) H59).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E D F) as H61.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E A D F) /\ ((euclidean__axioms.Cong E A F D) /\ (euclidean__axioms.Cong A E D F))) as H61.
------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (E) (F) (D) H60).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E A D F) /\ ((euclidean__axioms.Cong E A F D) /\ (euclidean__axioms.Cong A E D F))) as H62.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Cong E A F D) /\ (euclidean__axioms.Cong A E D F)) as H64.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- destruct H64 as [H64 H65].
exact H65.
------------------------------------------------------------ exact H61.
-------------------------------------------------------- assert (euclidean__axioms.BetS A E D \/ D = E) as H58.
--------------------------------------------------------- exact H57.
--------------------------------------------------------- destruct H58 as [H58|H58].
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D E A) as H59.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H59.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (D) H58).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D F) as H60.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H60.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (A) (E) (D) (F) (H58) H1).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D A E F) as H61.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A E F) /\ ((euclidean__axioms.Cong D A F E) /\ (euclidean__axioms.Cong A D E F))) as H61.
-------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (D) (F) (E) H10).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E F) /\ ((euclidean__axioms.Cong D A F E) /\ (euclidean__axioms.Cong A D E F))) as H62.
--------------------------------------------------------------- exact H61.
--------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Cong D A F E) /\ (euclidean__axioms.Cong A D E F)) as H64.
---------------------------------------------------------------- exact H63.
---------------------------------------------------------------- destruct H64 as [H64 H65].
exact H62.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D F) as H62.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H62.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (D) (E) (A) (E) (D) (F) (H54) (H61) (H59) H60).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E D F) as H63.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A E F D) /\ ((euclidean__axioms.Cong A E D F) /\ (euclidean__axioms.Cong E A F D))) as H63.
---------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (A) (D) (F) H62).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A E F D) /\ ((euclidean__axioms.Cong A E D F) /\ (euclidean__axioms.Cong E A F D))) as H64.
----------------------------------------------------------------- exact H63.
----------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Cong A E D F) /\ (euclidean__axioms.Cong E A F D)) as H66.
------------------------------------------------------------------ exact H65.
------------------------------------------------------------------ destruct H66 as [H66 H67].
exact H66.
--------------------------------------------------------------- exact H63.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E E F) as H59.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H59.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> (euclidean__axioms.Cong A E E F))))))))))))))))))))))))))))))) with (x := D).
-------------------------------------------------------------intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
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
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> (euclidean__axioms.Cong A E0 E0 F)))))))))))))))))))))))))))))))))))))))))))) with (y := E).
--------------------------------------------------------------intro H89.
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
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
assert (* Cut *) (e = e) as H131.
--------------------------------------------------------------- exact H112.
--------------------------------------------------------------- exact H99.

-------------------------------------------------------------- exact H27.
-------------------------------------------------------------- exact H60.
-------------------------------------------------------------- exact H0.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- exact H2.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- exact H62.
-------------------------------------------------------------- exact H6.
-------------------------------------------------------------- exact H7.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- exact H9.
-------------------------------------------------------------- exact H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- exact H13.
-------------------------------------------------------------- exact H15.
-------------------------------------------------------------- exact H19.
-------------------------------------------------------------- exact H24.
-------------------------------------------------------------- exact H25.
-------------------------------------------------------------- exact H26.
-------------------------------------------------------------- exact H28.
-------------------------------------------------------------- exact H29.
-------------------------------------------------------------- exact H76.
-------------------------------------------------------------- exact H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- exact H79.
-------------------------------------------------------------- exact H78.
-------------------------------------------------------------- exact H77.
-------------------------------------------------------------- exact H88.
-------------------------------------------------------------- exact H87.
-------------------------------------------------------------- exact H86.
-------------------------------------------------------------- exact H85.
-------------------------------------------------------------- exact H84.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- exact H82.
-------------------------------------------------------------- exact H81.
-------------------------------------------------------------- exact H80.

------------------------------------------------------------- exact H58.
------------------------------------------------------------- exact H.
------------------------------------------------------------- exact H1.
------------------------------------------------------------- exact H20.
------------------------------------------------------------- exact H21.
------------------------------------------------------------- exact H4.
------------------------------------------------------------- exact H5.
------------------------------------------------------------- exact H8.
------------------------------------------------------------- exact H10.
------------------------------------------------------------- exact H11.
------------------------------------------------------------- exact H12.
------------------------------------------------------------- exact H30.
------------------------------------------------------------- exact H31.
------------------------------------------------------------- exact H32.
------------------------------------------------------------- exact H33.
------------------------------------------------------------- exact H34.
------------------------------------------------------------- exact H35.
------------------------------------------------------------- exact H36.
------------------------------------------------------------- exact H40.
------------------------------------------------------------- exact H41.
------------------------------------------------------------- exact H42.
------------------------------------------------------------- exact H59.
------------------------------------------------------------- exact H47.
------------------------------------------------------------- exact H48.
------------------------------------------------------------- exact H49.
------------------------------------------------------------- exact H50.
------------------------------------------------------------- exact H51.
------------------------------------------------------------- exact H52.
------------------------------------------------------------- exact H53.
------------------------------------------------------------- exact H54.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E D F) as H60.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H60.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> (euclidean__axioms.Cong A E D0 F))))))))))))))))))))))))))))))) with (x := D).
--------------------------------------------------------------intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
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
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong A E0 E0 F) -> (euclidean__axioms.Cong A E0 E0 F))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
---------------------------------------------------------------intro H90.
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
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
assert (* Cut *) (e = e) as H133.
---------------------------------------------------------------- exact H113.
---------------------------------------------------------------- exact H132.

--------------------------------------------------------------- exact H27.
--------------------------------------------------------------- exact H61.
--------------------------------------------------------------- exact H0.
--------------------------------------------------------------- exact H62.
--------------------------------------------------------------- exact H2.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- exact H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- exact H63.
--------------------------------------------------------------- exact H6.
--------------------------------------------------------------- exact H7.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- exact H9.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- exact H13.
--------------------------------------------------------------- exact H15.
--------------------------------------------------------------- exact H19.
--------------------------------------------------------------- exact H24.
--------------------------------------------------------------- exact H25.
--------------------------------------------------------------- exact H26.
--------------------------------------------------------------- exact H28.
--------------------------------------------------------------- exact H29.
--------------------------------------------------------------- exact H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- exact H75.
--------------------------------------------------------------- exact H74.
--------------------------------------------------------------- exact H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- exact H80.
--------------------------------------------------------------- exact H79.
--------------------------------------------------------------- exact H78.
--------------------------------------------------------------- exact H89.
--------------------------------------------------------------- exact H88.
--------------------------------------------------------------- exact H87.
--------------------------------------------------------------- exact H86.
--------------------------------------------------------------- exact H85.
--------------------------------------------------------------- exact H84.
--------------------------------------------------------------- exact H83.
--------------------------------------------------------------- exact H82.
--------------------------------------------------------------- exact H81.
--------------------------------------------------------------- exact H59.

-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- exact H.
-------------------------------------------------------------- exact H1.
-------------------------------------------------------------- exact H20.
-------------------------------------------------------------- exact H21.
-------------------------------------------------------------- exact H4.
-------------------------------------------------------------- exact H5.
-------------------------------------------------------------- exact H8.
-------------------------------------------------------------- exact H10.
-------------------------------------------------------------- exact H11.
-------------------------------------------------------------- exact H12.
-------------------------------------------------------------- exact H30.
-------------------------------------------------------------- exact H31.
-------------------------------------------------------------- exact H32.
-------------------------------------------------------------- exact H33.
-------------------------------------------------------------- exact H34.
-------------------------------------------------------------- exact H35.
-------------------------------------------------------------- exact H36.
-------------------------------------------------------------- exact H40.
-------------------------------------------------------------- exact H41.
-------------------------------------------------------------- exact H42.
-------------------------------------------------------------- exact H60.
-------------------------------------------------------------- exact H47.
-------------------------------------------------------------- exact H48.
-------------------------------------------------------------- exact H49.
-------------------------------------------------------------- exact H50.
-------------------------------------------------------------- exact H51.
-------------------------------------------------------------- exact H52.
-------------------------------------------------------------- exact H53.
-------------------------------------------------------------- exact H54.
------------------------------------------------------------ exact H60.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D F A E) as H56.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H56.
----------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (E) (F) H55).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D C A B) as H57.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H57.
------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (B) (C) H53).
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H58.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H58.
------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------- apply (@proposition__04.proposition__04 (D) (F) (C) (A) (E) (B) (H56) (H57) H52).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F D E A) as H59.
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* Cut *) ((euclidean__axioms.Cong F D E A) /\ ((euclidean__axioms.Cong F D A E) /\ (euclidean__axioms.Cong D F E A))) as H63.
---------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (F) (A) (E) H56).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F D E A) /\ ((euclidean__axioms.Cong F D A E) /\ (euclidean__axioms.Cong D F E A))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Cong F D A E) /\ (euclidean__axioms.Cong D F E A)) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
exact H64.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B E D C F) as H60.
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H60.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H64.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (C) (F) (A) (B) (E) H63).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D C F) as H61.
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H61.
---------------------------------------------------------- exact H58.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H65.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (D) (C) (F)).
-------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (D) (C) (F)).
--------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (E) (D) (C) (F) H60).


--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F D C) as H62.
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H62.
----------------------------------------------------------- exact H58.
----------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* Cut *) ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol D F C) /\ (euclidean__axioms.nCol F C D))))) as H66.
------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (C) (F) H61).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol D F C) /\ (euclidean__axioms.nCol F C D))))) as H67.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol D F C) /\ (euclidean__axioms.nCol F C D)))) as H69.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol D F C) /\ (euclidean__axioms.nCol F C D))) as H71.
---------------------------------------------------------------- exact H70.
---------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol D F C) /\ (euclidean__axioms.nCol F C D)) as H73.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle F D C) as H63.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H63.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------ exact H62.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 F D C E A B) as H64.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H64.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H65.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (euclidean__axioms.BetS A D E \/ (euclidean__axioms.BetS A E D) \/ (D = E)) as H69.
---------------------------------------------------------------- exact H64.
---------------------------------------------------------------- destruct H69 as [H69|H69].
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H59.
------------------------------------------------------------------ split.
------------------------------------------------------------------- exact H57.
------------------------------------------------------------------- exact H65.
----------------------------------------------------------------- assert (euclidean__axioms.BetS A E D \/ D = E) as H70.
------------------------------------------------------------------ exact H69.
------------------------------------------------------------------ destruct H70 as [H70|H70].
------------------------------------------------------------------- split.
-------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H57.
--------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- split.
-------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H57.
--------------------------------------------------------------------- exact H65.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F D C E A B) as H65.
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H65.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H69.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (F) (D) (C) (E) (A) (B) H64).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H66.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H66.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E)))).
----------------------------------------------------------------intro H66.
assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H67.
----------------------------------------------------------------- exact H58.
----------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H69.
------------------------------------------------------------------ exact H68.
------------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* Cut *) (False) as H71.
------------------------------------------------------------------- apply (@H46 H66).
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) -> False) as H72.
-------------------------------------------------------------------- intro H72.
apply (@H66).
---------------------------------------------------------------------left.
exact H72.

-------------------------------------------------------------------- assert (* Cut *) (((euclidean__axioms.BetS A E D) \/ (D = E)) -> False) as H73.
--------------------------------------------------------------------- intro H73.
apply (@H66).
----------------------------------------------------------------------right.
exact H73.

--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A E D) -> False) as H74.
---------------------------------------------------------------------- intro H74.
apply (@H73).
-----------------------------------------------------------------------left.
exact H74.

---------------------------------------------------------------------- assert (* Cut *) ((D = E) -> False) as H75.
----------------------------------------------------------------------- intro H75.
apply (@H73).
------------------------------------------------------------------------right.
exact H75.

----------------------------------------------------------------------- assert False.
------------------------------------------------------------------------exact H71.
------------------------------------------------------------------------ contradiction.

--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as __TmpHyp.
----------------------------------------------------------------- exact H67.
----------------------------------------------------------------- assert (euclidean__axioms.BetS A D E \/ (euclidean__axioms.BetS A E D) \/ (D = E)) as H68.
------------------------------------------------------------------ exact __TmpHyp.
------------------------------------------------------------------ destruct H68 as [H68|H68].
------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H69.
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H69.
--------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H71.
---------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H73.
----------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (B) (C) (D) H).
-------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H70.
--------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------- destruct H70 as [M H70].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H71.
---------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H73.
----------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H75.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* Cut *) (euclidean__axioms.BetS D M B) as H77.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H77.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (D) H72).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H78.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)))) as H78.
--------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (A) (B) H30).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)))) as H79.
---------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B))) as H81.
----------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)) as H83.
------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
exact H48.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D E) as H79.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H79.
---------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H68.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D A) as H80.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H80.
----------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------- right.
left.
exact H39.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H81.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H81.
------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (E) H68).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H82.
------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E)) as H84.
-------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H82.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H82.
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (B)).
--------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (B)).
---------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (D) (B) (A) (E) (H78) (H80) (H79) H81).


------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B M D) as H83.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H83.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (euclidean__axioms.BetS B M D))))) with (x := e).
---------------------------------------------------------------------------------intro H84.
intro H85.
intro H86.
exact H72.

--------------------------------------------------------------------------------- exact H27.
--------------------------------------------------------------------------------- exact H18.
--------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------- assert (* Cut *) (exists (H84: euclidean__axioms.Point), (euclidean__axioms.BetS B H84 E) /\ (euclidean__axioms.BetS A M H84)) as H84.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H84.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (B) (A) (D) (M) (E) (H83) (H68) H82).
-------------------------------------------------------------------------------- assert (exists H85: euclidean__axioms.Point, ((euclidean__axioms.BetS B H85 E) /\ (euclidean__axioms.BetS A M H85))) as H86.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H86 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.BetS B H85 E) /\ (euclidean__axioms.BetS A M H85)) as H87.
---------------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* Cut *) (euclidean__axioms.Col A M H85) as H89.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H89.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H88.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A M C) as H90.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H90.
------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H71.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A M) as H91.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M H85) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H85))) as H91.
-------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (H85) H88).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M H85) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H85))) as H92.
--------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H85)) as H94.
---------------------------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H94.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H92.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H92.
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (M) H91).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A H85) as H93.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M A H85) /\ ((euclidean__axioms.Col M H85 A) /\ ((euclidean__axioms.Col H85 A M) /\ ((euclidean__axioms.Col A H85 M) /\ (euclidean__axioms.Col H85 M A))))) as H93.
---------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (M) (H85) H89).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M A H85) /\ ((euclidean__axioms.Col M H85 A) /\ ((euclidean__axioms.Col H85 A M) /\ ((euclidean__axioms.Col A H85 M) /\ (euclidean__axioms.Col H85 M A))))) as H94.
----------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col M H85 A) /\ ((euclidean__axioms.Col H85 A M) /\ ((euclidean__axioms.Col A H85 M) /\ (euclidean__axioms.Col H85 M A)))) as H96.
------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col H85 A M) /\ ((euclidean__axioms.Col A H85 M) /\ (euclidean__axioms.Col H85 M A))) as H98.
------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col A H85 M) /\ (euclidean__axioms.Col H85 M A)) as H100.
-------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H94.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A C) as H94.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H94.
----------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (M) (C) H90).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A)))) as H97.
------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))) as H99.
-------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A)) as H101.
--------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H95.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H85 C) as H95.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H95.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (H85) (C)).
-------------------------------------------------------------------------------------------intro H96.
apply (@euclidean__tactics.Col__nCol__False (A) (H85) (C) (H96)).
--------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (A) (H85) (C) (H93) (H94) H92).


----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E H85 B) as H96.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H96.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (H85) (E) H87).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E A) as H97.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H97.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (E) H81).
------------------------------------------------------------------------------------------- assert (* Cut *) (~(B = C)) as H98.
-------------------------------------------------------------------------------------------- intro H98.
assert (* Cut *) (euclidean__axioms.Col A B C) as H99.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H99.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------- right.
right.
left.
exact H98.
--------------------------------------------------------------------------------------------- apply (@H46).
----------------------------------------------------------------------------------------------intro H100.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H43) H99).

-------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H99.
--------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H99.
---------------------------------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
----------------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H100.
------------------------------------------------------------------------------------------------ exact __TmpHyp0.
------------------------------------------------------------------------------------------------ destruct H100 as [x H100].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H101.
------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------- destruct H101 as [x0 H101].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H102.
-------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------- destruct H102 as [x1 H102].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H103.
--------------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------------- destruct H103 as [x2 H103].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H104.
---------------------------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------------------------- destruct H104 as [x3 H104].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H105.
----------------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H107.
------------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H109.
------------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H111.
-------------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H113.
--------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H115.
---------------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H117.
----------------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H119.
------------------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* AndElim *) ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H121.
------------------------------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H123.
-------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H125.
--------------------------------------------------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
---------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H126.
----------------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
----------------------------------------------------------------------------------------------------------------- destruct H126 as [x4 H126].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H127.
------------------------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------------------------ destruct H127 as [x5 H127].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H128.
------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------- destruct H128 as [x6 H128].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H129.
-------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------- destruct H129 as [x7 H129].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H130.
--------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------- destruct H130 as [x8 H130].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H131.
---------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H133.
----------------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H135.
------------------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H137.
------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H139.
-------------------------------------------------------------------------------------------------------------------------- exact H138.
-------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H141.
--------------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H143.
---------------------------------------------------------------------------------------------------------------------------- exact H142.
---------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H145.
----------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H147.
------------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------------ destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H149.
------------------------------------------------------------------------------------------------------------------------------- exact H148.
------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H151.
-------------------------------------------------------------------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
--------------------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
---------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [x9 H152].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H153.
----------------------------------------------------------------------------------------------------------------------------------- exact H152.
----------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [x10 H153].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H154.
------------------------------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------------------------------ destruct H154 as [x11 H154].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H155.
------------------------------------------------------------------------------------------------------------------------------------- exact H154.
------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [x12 H155].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H156.
-------------------------------------------------------------------------------------------------------------------------------------- exact H155.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [x13 H156].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H157.
--------------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H159.
---------------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H161.
----------------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H163.
------------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H167.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H169.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H171.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H173.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H175.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H174.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H175 as [H175 H176].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H20.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H178.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [x14 H178].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H179.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [x15 H179].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H180.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [x16 H180].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H181.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H181 as [x17 H181].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [x18 H182].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H183.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H185.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H187.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H189.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H195.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H197.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H199.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H201.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
exact H173.
--------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E A C B)) as H100.
---------------------------------------------------------------------------------------------- intro H100.
assert (* Cut *) (exists (q: euclidean__axioms.Point), (euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E A q) /\ (euclidean__axioms.Col C B q)))) as H101.
----------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------- assert (exists q: euclidean__axioms.Point, ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E A q) /\ (euclidean__axioms.Col C B q))))) as H102.
------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------ destruct H102 as [q H102].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E A q) /\ (euclidean__axioms.Col C B q)))) as H103.
------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E A q) /\ (euclidean__axioms.Col C B q))) as H105.
-------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col E A q) /\ (euclidean__axioms.Col C B q)) as H107.
--------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* Cut *) (euclidean__axioms.neq B C) as H109.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H109.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (euclidean__axioms.neq B C))))) with (x := e).
------------------------------------------------------------------------------------------------------intro H110.
intro H111.
intro H112.
exact H98.

------------------------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------------------------ exact H18.
------------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------------ exact H23.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C q) as H110.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H110.
------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (q) H108).
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H111.
------------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)))) as H113.
-------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))) as H115.
--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)) as H117.
---------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H111.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E q) as H111.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A E q) /\ ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))))) as H111.
------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (q) H107).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E q) /\ ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))))) as H112.
-------------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E)))) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H112.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A D E) as H112.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H112.
-------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H113.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H113.
--------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H112).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H114.
---------------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H116.
----------------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H118.
------------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H120.
------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H118.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A q) as H114.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H114.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (D) H113).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))))) as H115.
----------------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)))) as H117.
------------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------------ destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E))) as H119.
------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ (euclidean__axioms.Col D A E)) as H121.
-------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
exact H107.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H115.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H85 B) /\ ((euclidean__axioms.neq E H85) /\ (euclidean__axioms.neq E B))) as H115.
----------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H85) (B) H96).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H85 B) /\ ((euclidean__axioms.neq E H85) /\ (euclidean__axioms.neq E B))) as H116.
------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq E H85) /\ (euclidean__axioms.neq E B)) as H118.
------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H42.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D q) as H116.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H116.
------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (D) (q)).
-------------------------------------------------------------------------------------------------------------intro H117.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (q) (H117)).
--------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (D) (q) (H113) (H114) H103).


----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H117.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H117.
------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------- exists q.
split.
-------------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------------------ apply (@H46).
-------------------------------------------------------------------------------------------------------------intro H118.
apply (@H99 H117).

---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C H85) as H101.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H85 A C) /\ ((euclidean__axioms.Col H85 C A) /\ ((euclidean__axioms.Col C A H85) /\ ((euclidean__axioms.Col A C H85) /\ (euclidean__axioms.Col C H85 A))))) as H101.
------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (H85) (C) H95).
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col H85 A C) /\ ((euclidean__axioms.Col H85 C A) /\ ((euclidean__axioms.Col C A H85) /\ ((euclidean__axioms.Col A C H85) /\ (euclidean__axioms.Col C H85 A))))) as H102.
------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col H85 C A) /\ ((euclidean__axioms.Col C A H85) /\ ((euclidean__axioms.Col A C H85) /\ (euclidean__axioms.Col C H85 A)))) as H104.
-------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col C A H85) /\ ((euclidean__axioms.Col A C H85) /\ (euclidean__axioms.Col C H85 A))) as H106.
--------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col A C H85) /\ (euclidean__axioms.Col C H85 A)) as H108.
---------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
exact H108.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A A) as H102.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H102.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------- right.
right.
left.
exact H39.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C C B) as H103.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H103.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------- left.
exact H37.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H104.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H104.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H98).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A H85 C) as H105.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H105.
---------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (E) (A) (C) (B) (A) (C) (H85) (H102) (H103) (H97) (H104) (H97) (H104) (H100) (H96) H101).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H85 A) as H106.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H106.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (H85) (C) H105).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D A) as H107.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H107.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (E) H68).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D C) as H108.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)))) as H108.
------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (A) (B) H30).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)))) as H109.
-------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B))) as H111.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol D C B)) as H113.
---------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
exact H40.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A D E) as H109.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H109.
-------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H110.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H110.
--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (C)).
----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (C)).
-----------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (D) (C) (A) (E) (H108) (H80) (H109) H81).


-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A E) as H111.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H111.
---------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (C) H110).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H112.
----------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)))) as H114.
------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))) as H116.
------------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)) as H118.
-------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H116.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS C G D) /\ (euclidean__axioms.BetS E G H85)) as H112.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H112.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (C) (E) (A) (H85) (D) (H106) (H107) H111).
---------------------------------------------------------------------------------------------------------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.BetS E G H85))) as H113.
----------------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------------- destruct H113 as [G H113].
assert (* AndElim *) ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.BetS E G H85)) as H114.
------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* Cut *) (euclidean__axioms.BetS E G B) as H116.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H116.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (E) (G) (H85) (B) (H115) H96).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G B) as H117.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H117.
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (euclidean__axioms.BetS E G B))))) with (x := e).
----------------------------------------------------------------------------------------------------------------intro H118.
intro H119.
intro H120.
exact H116.

---------------------------------------------------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------------------------------------------------- exact H18.
---------------------------------------------------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E G B) as H118.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H118.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H117.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D E G)) as H119.
---------------------------------------------------------------------------------------------------------------- intro H119.
assert (* Cut *) (euclidean__axioms.Col G E D) as H120.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D G) /\ ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col D G E) /\ (euclidean__axioms.Col G E D))))) as H120.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (G) H119).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col E D G) /\ ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col D G E) /\ (euclidean__axioms.Col G E D))))) as H121.
------------------------------------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col D G E) /\ (euclidean__axioms.Col G E D)))) as H123.
-------------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col D G E) /\ (euclidean__axioms.Col G E D))) as H125.
--------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col D G E) /\ (euclidean__axioms.Col G E D)) as H127.
---------------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H128.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G E B) as H121.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G E B) /\ ((euclidean__axioms.Col G B E) /\ ((euclidean__axioms.Col B E G) /\ ((euclidean__axioms.Col E B G) /\ (euclidean__axioms.Col B G E))))) as H121.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (G) (B) H118).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G E B) /\ ((euclidean__axioms.Col G B E) /\ ((euclidean__axioms.Col B E G) /\ ((euclidean__axioms.Col E B G) /\ (euclidean__axioms.Col B G E))))) as H122.
-------------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col G B E) /\ ((euclidean__axioms.Col B E G) /\ ((euclidean__axioms.Col E B G) /\ (euclidean__axioms.Col B G E)))) as H124.
--------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col B E G) /\ ((euclidean__axioms.Col E B G) /\ (euclidean__axioms.Col B G E))) as H126.
---------------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col E B G) /\ (euclidean__axioms.Col B G E)) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H122.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E G) as H122.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H122.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (B) H117).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H123.
--------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B)) as H125.
---------------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
exact H125.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G E) as H123.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H123.
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (G) H122).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D B) as H124.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H124.
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (D) (B)).
-----------------------------------------------------------------------------------------------------------------------intro H125.
apply (@euclidean__tactics.Col__nCol__False (E) (D) (B) (H125)).
------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (E) (D) (B) (H120) (H121) H123).


--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H125.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H125.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------- right.
left.
exact H38.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H126.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H126.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H109).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H127.
------------------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H129.
-------------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H131.
--------------------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H133.
---------------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H134.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D D) as H127.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H127.
------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H36.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D E) as H128.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H128.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (E) H68).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H129.
--------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E)) as H131.
---------------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
exact H129.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H129.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H129.
--------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H128).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D B) as H130.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H130.
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (D) (B)).
-----------------------------------------------------------------------------------------------------------------------------intro H131.
apply (@euclidean__tactics.Col__nCol__False (A) (D) (B) (H131)).
------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (E) (D) (A) (D) (B) (H129) (H126) (H127) H124).


--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H131.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H131.
----------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------------- exists B.
split.
------------------------------------------------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------- exact H130.
-------------------------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------------------- apply (@H46).
-----------------------------------------------------------------------------------------------------------------------------intro H132.
apply (@H99 H131).

---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle D E G) as H120.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H120.
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (D) (E) (G) H119).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D E G D E G) as H121.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H121.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------- apply (@lemma__ETreflexive.lemma__ETreflexive (D) (E) (G) H120).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET D E G E D G) as H122.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET D E G E G D) /\ ((euclidean__axioms.ET D E G D G E) /\ ((euclidean__axioms.ET D E G E D G) /\ ((euclidean__axioms.ET D E G G E D) /\ (euclidean__axioms.ET D E G G D E))))) as H122.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (D) (E) (G) (D) (E) (G) H121).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET D E G E G D) /\ ((euclidean__axioms.ET D E G D G E) /\ ((euclidean__axioms.ET D E G E D G) /\ ((euclidean__axioms.ET D E G G E D) /\ (euclidean__axioms.ET D E G G D E))))) as H123.
--------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.ET D E G D G E) /\ ((euclidean__axioms.ET D E G E D G) /\ ((euclidean__axioms.ET D E G G E D) /\ (euclidean__axioms.ET D E G G D E)))) as H125.
---------------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.ET D E G E D G) /\ ((euclidean__axioms.ET D E G G E D) /\ (euclidean__axioms.ET D E G G D E))) as H127.
----------------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.ET D E G G E D) /\ (euclidean__axioms.ET D E G G D E)) as H129.
------------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------------ destruct H129 as [H129 H130].
exact H127.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F D C A E B) as H123.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F D C A B E) /\ ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))))) as H123.
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (D) (C) (E) (A) (B) H65).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F D C A B E) /\ ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))))) as H124.
---------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A)))) as H126.
----------------------------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))) as H128.
------------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A)) as H130.
------------------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
exact H128.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B F D C) as H124.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H124.
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (F) (D) (C) (A) (E) (B) H123).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B G E) as H125.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H125.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (G) (B) H117).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D E F) as H126.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H126.
------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__3__6a.lemma__3__6a (A) (D) (E) (F) (H68) H29).
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E D) as H127.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H127.
------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (E) (F) H126).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A D G B F E G C) as H128.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H128.
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__cutoff1 (A) (D) (E) (G) (B) (F) (E) (D) (G) (C) (H68) (H127) (H125) (H114) (H122) H124).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E G D) as H129.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E D G) /\ ((euclidean__axioms.nCol E G D) /\ ((euclidean__axioms.nCol G D E) /\ ((euclidean__axioms.nCol D G E) /\ (euclidean__axioms.nCol G E D))))) as H129.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (E) (G) H120).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E D G) /\ ((euclidean__axioms.nCol E G D) /\ ((euclidean__axioms.nCol G D E) /\ ((euclidean__axioms.nCol D G E) /\ (euclidean__axioms.nCol G E D))))) as H130.
---------------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.nCol E G D) /\ ((euclidean__axioms.nCol G D E) /\ ((euclidean__axioms.nCol D G E) /\ (euclidean__axioms.nCol G E D)))) as H132.
----------------------------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.nCol G D E) /\ ((euclidean__axioms.nCol D G E) /\ (euclidean__axioms.nCol G E D))) as H134.
------------------------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.nCol D G E) /\ (euclidean__axioms.nCol G E D)) as H136.
------------------------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H132.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (G = G) as H130.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H130.
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) G).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E G G) as H131.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H131.
----------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H130.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H132.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H132.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (B) H117).
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H133.
------------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B)) as H135.
-------------------------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
exact H133.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H133.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H133.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (B) H132).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B G D) as H134.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H134.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (G) (D)).
---------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (G) (D)).
----------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (E) (G) (D) (B) (G) (H129) (H118) (H131) H133).


------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D G B) as H135.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G B D) /\ ((euclidean__axioms.nCol G D B) /\ ((euclidean__axioms.nCol D B G) /\ ((euclidean__axioms.nCol B D G) /\ (euclidean__axioms.nCol D G B))))) as H135.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (G) (D) H134).
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G B D) /\ ((euclidean__axioms.nCol G D B) /\ ((euclidean__axioms.nCol D B G) /\ ((euclidean__axioms.nCol B D G) /\ (euclidean__axioms.nCol D G B))))) as H136.
---------------------------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.nCol G D B) /\ ((euclidean__axioms.nCol D B G) /\ ((euclidean__axioms.nCol B D G) /\ (euclidean__axioms.nCol D G B)))) as H138.
----------------------------------------------------------------------------------------------------------------------------------- exact H137.
----------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.nCol D B G) /\ ((euclidean__axioms.nCol B D G) /\ (euclidean__axioms.nCol D G B))) as H140.
------------------------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.nCol B D G) /\ (euclidean__axioms.nCol D G B)) as H142.
------------------------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
exact H143.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G D) as H136.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H136.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H114.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G C) as H137.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H137.
----------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (D) H136).
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H138.
------------------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C)))) as H140.
------------------------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))) as H142.
-------------------------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C)) as H144.
--------------------------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
exact H145.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G G) as H138.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H138.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------------------ right.
right.
left.
exact H130.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H139.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H139.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (G) (D) H114).
------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H140.
-------------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D)) as H142.
--------------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
exact H142.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C G B) as H140.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H140.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (G) (B)).
---------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (G) (B)).
----------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (D) (G) (B) (C) (G) (H135) (H137) (H138) H139).


------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G C B) as H141.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G C B) /\ ((euclidean__axioms.nCol G B C) /\ ((euclidean__axioms.nCol B C G) /\ ((euclidean__axioms.nCol C B G) /\ (euclidean__axioms.nCol B G C))))) as H141.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (G) (B) H140).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G C B) /\ ((euclidean__axioms.nCol G B C) /\ ((euclidean__axioms.nCol B C G) /\ ((euclidean__axioms.nCol C B G) /\ (euclidean__axioms.nCol B G C))))) as H142.
---------------------------------------------------------------------------------------------------------------------------------------- exact H141.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.nCol G B C) /\ ((euclidean__axioms.nCol B C G) /\ ((euclidean__axioms.nCol C B G) /\ (euclidean__axioms.nCol B G C)))) as H144.
----------------------------------------------------------------------------------------------------------------------------------------- exact H143.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.nCol B C G) /\ ((euclidean__axioms.nCol C B G) /\ (euclidean__axioms.nCol B G C))) as H146.
------------------------------------------------------------------------------------------------------------------------------------------ exact H145.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.nCol C B G) /\ (euclidean__axioms.nCol B G C)) as H148.
------------------------------------------------------------------------------------------------------------------------------------------- exact H147.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
exact H142.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle G C B) as H142.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H142.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET G C B G C B) as H143.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H143.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ETreflexive.lemma__ETreflexive (G) (C) (B) H142).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET G C B G B C) as H144.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET G C B C B G) /\ ((euclidean__axioms.ET G C B G B C) /\ ((euclidean__axioms.ET G C B C G B) /\ ((euclidean__axioms.ET G C B B C G) /\ (euclidean__axioms.ET G C B B G C))))) as H144.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (G) (C) (B) (G) (C) (B) H143).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET G C B C B G) /\ ((euclidean__axioms.ET G C B G B C) /\ ((euclidean__axioms.ET G C B C G B) /\ ((euclidean__axioms.ET G C B B C G) /\ (euclidean__axioms.ET G C B B G C))))) as H145.
------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.ET G C B G B C) /\ ((euclidean__axioms.ET G C B C G B) /\ ((euclidean__axioms.ET G C B B C G) /\ (euclidean__axioms.ET G C B B G C)))) as H147.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.ET G C B C G B) /\ ((euclidean__axioms.ET G C B B C G) /\ (euclidean__axioms.ET G C B B G C))) as H149.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.ET G C B B C G) /\ (euclidean__axioms.ET G C B B G C)) as H151.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H150.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
exact H147.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D G C) as H145.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H145.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (G) (D) H114).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG B C D A) as H146.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H146.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (A) (B) (C) (D) H).
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG D A B C) as H147.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H147.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGsymmetric.lemma__PGsymmetric (B) (C) (D) (A) H146).
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A D C B) as H148.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H148.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip (D) (A) (B) (C) H147).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (q: euclidean__axioms.Point), (euclidean__axioms.BetS A q C) /\ (euclidean__axioms.BetS D q B)) as H149.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H149.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (D) (C) (B) H148).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (exists q: euclidean__axioms.Point, ((euclidean__axioms.BetS A q C) /\ (euclidean__axioms.BetS D q B))) as H150.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [q H150].
assert (* AndElim *) ((euclidean__axioms.BetS A q C) /\ (euclidean__axioms.BetS D q B)) as H151.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H151 H152].
assert (* Cut *) (euclidean__defs.PG B C F E) as H153.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H153.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (E) (B) (C) (F) H0).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG C F E B) as H154.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H154.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (B) (C) (F) (E) H153).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG F E B C) as H155.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H155.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (C) (F) (E) (B) H154).
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS F m B) /\ (euclidean__axioms.BetS E m C)) as H156.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H156.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (F) (E) (B) (C) H155).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS F m B) /\ (euclidean__axioms.BetS E m C))) as H157.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [m H157].
assert (* AndElim *) ((euclidean__axioms.BetS F m B) /\ (euclidean__axioms.BetS E m C)) as H158.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H157.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H158 as [H158 H159].
assert (* Cut *) (euclidean__axioms.EF A D C B F E B C) as H160.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H160.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste2 (A) (D) (G) (C) (B) (q) (F) (E) (G) (B) (C) (m) (H145) (H117) (H144) (H128) (H151) (H152) (H158) H159).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A D C B E B C F) as H161.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF A D C B E B C F) /\ ((euclidean__axioms.EF A D C B C B E F) /\ ((euclidean__axioms.EF A D C B B C F E) /\ ((euclidean__axioms.EF A D C B E F C B) /\ ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E))))))) as H161.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (A) (D) (C) (B) (F) (E) (B) (C) H160).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF A D C B E B C F) /\ ((euclidean__axioms.EF A D C B C B E F) /\ ((euclidean__axioms.EF A D C B B C F E) /\ ((euclidean__axioms.EF A D C B E F C B) /\ ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E))))))) as H162.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.EF A D C B C B E F) /\ ((euclidean__axioms.EF A D C B B C F E) /\ ((euclidean__axioms.EF A D C B E F C B) /\ ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E)))))) as H164.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.EF A D C B B C F E) /\ ((euclidean__axioms.EF A D C B E F C B) /\ ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E))))) as H166.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H165.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.EF A D C B E F C B) /\ ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E)))) as H168.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.EF A D C B C F E B) /\ ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E))) as H170.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.EF A D C B B E F C) /\ (euclidean__axioms.EF A D C B F C B E)) as H172.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
exact H162.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A D C B) as H162.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H162.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (A) (D) (C) (B) (E) (B) (C) (F) H161).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A B C D) as H163.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F C B A D) /\ ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D))))))) as H163.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (E) (B) (C) (F) (A) (D) (C) (B) H162).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F C B A D) /\ ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D))))))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H163.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F C B A D) /\ ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D)))))) as H166.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.EF E B C F C B A D) /\ ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D))))) as H168.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D)))) as H170.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D))) as H172.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.EF E B C F C D A B) /\ (euclidean__axioms.EF E B C F A B C D)) as H174.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
exact H175.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H164.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFsymmetric (E) (B) (C) (F) (A) (B) (C) (D) H163).
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
------------------------------------------------------------------- assert (euclidean__axioms.BetS A E D \/ D = E) as H69.
-------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------- destruct H69 as [H69|H69].
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E A B F D C) as H70.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H70.
----------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H72.
------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H74.
------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (F) (D) (C) (E) (A) (B) H65).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E A B D F C) as H71.
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H71.
------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H73.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* Cut *) ((euclidean__axioms.ET E A B D C F) /\ ((euclidean__axioms.ET E A B F C D) /\ ((euclidean__axioms.ET E A B D F C) /\ ((euclidean__axioms.ET E A B C D F) /\ (euclidean__axioms.ET E A B C F D))))) as H75.
-------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (E) (A) (B) (F) (D) (C) H70).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET E A B D C F) /\ ((euclidean__axioms.ET E A B F C D) /\ ((euclidean__axioms.ET E A B D F C) /\ ((euclidean__axioms.ET E A B C D F) /\ (euclidean__axioms.ET E A B C F D))))) as H76.
--------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.ET E A B F C D) /\ ((euclidean__axioms.ET E A B D F C) /\ ((euclidean__axioms.ET E A B C D F) /\ (euclidean__axioms.ET E A B C F D)))) as H78.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.ET E A B D F C) /\ ((euclidean__axioms.ET E A B C D F) /\ (euclidean__axioms.ET E A B C F D))) as H80.
----------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.ET E A B C D F) /\ (euclidean__axioms.ET E A B C F D)) as H82.
------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------ destruct H82 as [H82 H83].
exact H80.
----------------------------------------------------------------------- assert (* Cut *) (exists (H72: euclidean__axioms.Point), (euclidean__axioms.BetS B H72 D) /\ (euclidean__axioms.BetS C H72 E)) as H72.
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H72.
------------------------------------------------------------------------- exact H58.
------------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H74.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H76.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------- apply (@lemma__trapezoiddiagonals.lemma__trapezoiddiagonals (A) (B) (C) (D) (E) (H) H69).
------------------------------------------------------------------------ assert (exists H73: euclidean__axioms.Point, ((euclidean__axioms.BetS B H73 D) /\ (euclidean__axioms.BetS C H73 E))) as H74.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H74 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.BetS B H73 D) /\ (euclidean__axioms.BetS C H73 E)) as H75.
-------------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H77.
--------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H79.
---------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* Cut *) (euclidean__axioms.BetS E H73 C) as H81.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H81.
------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (H73) (E) H76).
----------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B E D)) as H82.
------------------------------------------------------------------------------ intro H82.
assert (* Cut *) (euclidean__axioms.Col A E D) as H83.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H83.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H69.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H84.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H84.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (D) H83).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H85.
---------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)))) as H87.
----------------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))) as H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)) as H91.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H87.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D B) as H85.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col E D B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B D E) /\ (euclidean__axioms.Col D E B))))) as H85.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (D) H82).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col E D B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B D E) /\ (euclidean__axioms.Col D E B))))) as H86.
----------------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col E D B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B D E) /\ (euclidean__axioms.Col D E B)))) as H88.
------------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------------ destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B D E) /\ (euclidean__axioms.Col D E B))) as H90.
------------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col B D E) /\ (euclidean__axioms.Col D E B)) as H92.
-------------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
exact H88.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H86.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A D))) as H86.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (D) H69).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A D))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A D)) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H87.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A B) as H87.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H87.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (D) (A) (B)).
-------------------------------------------------------------------------------------intro H88.
apply (@euclidean__tactics.Col__nCol__False (D) (A) (B) (H88)).
--------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (D) (A) (B) (H84) (H85) H86).


----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D B) as H88.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))))) as H88.
------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (B) H87).
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))))) as H89.
-------------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D)))) as H91.
--------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))) as H93.
---------------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D)) as H95.
----------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H89.
------------------------------------------------------------------------------------ assert (* Cut *) (B = B) as H89.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H89.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun e0: euclidean__axioms.Point => (euclidean__axioms.BetS F e0 A) -> ((euclidean__axioms.Cong F e0 F E) -> ((euclidean__defs.Out F A e0) -> (B = B))))) with (x := e).
---------------------------------------------------------------------------------------intro H90.
intro H91.
intro H92.
exact H38.

--------------------------------------------------------------------------------------- exact H27.
--------------------------------------------------------------------------------------- exact H18.
--------------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H90.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H90.
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------- right.
left.
exact H89.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H91.
--------------------------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H92.
---------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H92.
----------------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H93.
------------------------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------------------------- destruct H93 as [x H93].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H94.
-------------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------------- destruct H94 as [x0 H94].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H95.
--------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------- destruct H95 as [x1 H95].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H96.
---------------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------------- destruct H96 as [x2 H96].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H97.
----------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------- destruct H97 as [x3 H97].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H98.
------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H100.
------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H102.
-------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H104.
--------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H106.
---------------------------------------------------------------------------------------------------- exact H105.
---------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H108.
----------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H110.
------------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H112.
------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H114.
-------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H116.
--------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H118.
---------------------------------------------------------------------------------------------------------- exact H4.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H119.
------------------------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------------------------ destruct H119 as [x4 H119].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H120.
------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- destruct H120 as [x5 H120].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H121.
-------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------- destruct H121 as [x6 H121].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H122.
--------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------- destruct H122 as [x7 H122].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H123.
---------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------- destruct H123 as [x8 H123].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H126.
------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H128.
------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H130.
-------------------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H132.
--------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H134.
---------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H136.
----------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H138.
------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H140.
------------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H142.
-------------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H144.
--------------------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H145.
----------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------------------------- destruct H145 as [x9 H145].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H146.
------------------------------------------------------------------------------------------------------------------------------ exact H145.
------------------------------------------------------------------------------------------------------------------------------ destruct H146 as [x10 H146].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H147.
------------------------------------------------------------------------------------------------------------------------------- exact H146.
------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [x11 H147].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [x12 H148].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H149.
--------------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [x13 H149].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H150.
---------------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H152.
----------------------------------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H154.
------------------------------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------------------------------ destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H158.
-------------------------------------------------------------------------------------------------------------------------------------- exact H157.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H160.
--------------------------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H162.
---------------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H164.
----------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H166.
------------------------------------------------------------------------------------------------------------------------------------------ exact H165.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H168.
------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H170.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H20.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H171.
---------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [x14 H171].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H172.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [x15 H172].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H172.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H173 as [x16 H173].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H174.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [x17 H174].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [x18 H175].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H176.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H178.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H180.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H181.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H186.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H192.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H194 as [H194 H195].
exact H152.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H93.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H93.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------ exists B.
split.
------------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H94.
------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H94.
------------------------------------------------------------------------------------------- exact H30.
------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H95.
--------------------------------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------------------------------- destruct H95 as [x H95].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H96.
---------------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------------- destruct H96 as [x0 H96].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H97.
----------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------- destruct H97 as [x1 H97].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H98.
------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------ destruct H98 as [x2 H98].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H99.
------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------- destruct H99 as [x3 H99].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H100.
-------------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H102.
--------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col D C x) /\ ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H104.
---------------------------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col D C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H106.
----------------------------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H108.
------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------ destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H110.
------------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H112.
-------------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H120.
------------------------------------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H121.
-------------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
-------------------------------------------------------------------------------------------------------------- destruct H121 as [x4 H121].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H122.
--------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------- destruct H122 as [x5 H122].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H123.
---------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------- destruct H123 as [x6 H123].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [x7 H124].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H125.
------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [x8 H125].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H126.
------------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H128.
-------------------------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H130.
--------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H132.
---------------------------------------------------------------------------------------------------------------------- exact H131.
---------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H134.
----------------------------------------------------------------------------------------------------------------------- exact H133.
----------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col D C x6) /\ ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H136.
------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------ destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col D C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H138.
------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H140.
-------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H142.
--------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H144.
---------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H146.
----------------------------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H147.
------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [x9 H147].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [x10 H148].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H149.
--------------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [x11 H149].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H150.
---------------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [x12 H150].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H151.
----------------------------------------------------------------------------------------------------------------------------------- exact H150.
----------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [x13 H151].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H152.
------------------------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H154.
------------------------------------------------------------------------------------------------------------------------------------- exact H153.
------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col A D x9) /\ ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H156.
-------------------------------------------------------------------------------------------------------------------------------------- exact H155.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col A D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H158.
--------------------------------------------------------------------------------------------------------------------------------------- exact H157.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H160.
---------------------------------------------------------------------------------------------------------------------------------------- exact H159.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.Col B C x11) /\ ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H162.
----------------------------------------------------------------------------------------------------------------------------------------- exact H161.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col B C x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------ exact H163.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H166.
------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H168.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H170.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H172.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H20.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H173 as [x14 H173].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H174.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [x15 H174].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [x16 H175].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H176.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [x17 H176].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [x18 H177].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H179.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.Col C D x16) /\ ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.Col C D x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H191.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H192 as [H192 H193].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
exact H168.
------------------------------------------------------------------------------------------ apply (@H46).
-------------------------------------------------------------------------------------------intro H95.
apply (@H94 H93).

------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF B E D C B E D C) as H83.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H83.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------- apply (@lemma__EFreflexive.lemma__EFreflexive (B) (E) (D) (C) (H73) (H75) (H81)).
---------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (E) (D) H82).

------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B E D C C D E B) as H84.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B E D C E D C B) /\ ((euclidean__axioms.EF B E D C C D E B) /\ ((euclidean__axioms.EF B E D C D C B E) /\ ((euclidean__axioms.EF B E D C E B C D) /\ ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E))))))) as H84.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (B) (E) (D) (C) (B) (E) (D) (C) H83).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF B E D C E D C B) /\ ((euclidean__axioms.EF B E D C C D E B) /\ ((euclidean__axioms.EF B E D C D C B E) /\ ((euclidean__axioms.EF B E D C E B C D) /\ ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E))))))) as H85.
---------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.EF B E D C C D E B) /\ ((euclidean__axioms.EF B E D C D C B E) /\ ((euclidean__axioms.EF B E D C E B C D) /\ ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E)))))) as H87.
----------------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.EF B E D C D C B E) /\ ((euclidean__axioms.EF B E D C E B C D) /\ ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E))))) as H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.EF B E D C E B C D) /\ ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E)))) as H91.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.EF B E D C C B E D) /\ ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E))) as H93.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.EF B E D C D E B C) /\ (euclidean__axioms.EF B E D C B C D E)) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H87.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF C D E B B E D C) as H85.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H85.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (B) (E) (D) (C) (C) (D) (E) (B) H84).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D E A) as H86.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H86.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (D) H69).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D F) as H87.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H87.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------ apply (@lemma__3__6a.lemma__3__6a (A) (E) (D) (F) (H69) H1).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG C D A B) as H88.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H88.
------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------- apply (@lemma__PGsymmetric.lemma__PGsymmetric (A) (B) (C) (D) H).
------------------------------------------------------------------------------------ assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.BetS C p A) /\ (euclidean__axioms.BetS D p B)) as H89.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H89.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (C) (D) (A) (B) H88).
------------------------------------------------------------------------------------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.BetS C p A) /\ (euclidean__axioms.BetS D p B))) as H90.
-------------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------------- destruct H90 as [p H90].
assert (* AndElim *) ((euclidean__axioms.BetS C p A) /\ (euclidean__axioms.BetS D p B)) as H91.
--------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* Cut *) (euclidean__defs.PG B E F C) as H93.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H93.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip (E) (B) (C) (F) H0).
---------------------------------------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS B m F) /\ (euclidean__axioms.BetS E m C)) as H94.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H94.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (B) (E) (F) (C) H93).
----------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS B m F) /\ (euclidean__axioms.BetS E m C))) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ destruct H95 as [m H95].
assert (* AndElim *) ((euclidean__axioms.BetS B m F) /\ (euclidean__axioms.BetS E m C)) as H96.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* Cut *) (euclidean__axioms.EF C D A B B E F C) as H98.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H98.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste2 (C) (D) (E) (A) (B) (p) (B) (E) (D) (F) (C) (m) (H86) (H87) (H71) (H85) (H91) (H92) (H96) H97).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF C D A B E B C F) as H99.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF C D A B E F C B) /\ ((euclidean__axioms.EF C D A B C F E B) /\ ((euclidean__axioms.EF C D A B F C B E) /\ ((euclidean__axioms.EF C D A B E B C F) /\ ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E))))))) as H99.
---------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (C) (D) (A) (B) (B) (E) (F) (C) H98).
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF C D A B E F C B) /\ ((euclidean__axioms.EF C D A B C F E B) /\ ((euclidean__axioms.EF C D A B F C B E) /\ ((euclidean__axioms.EF C D A B E B C F) /\ ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E))))))) as H100.
----------------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.EF C D A B C F E B) /\ ((euclidean__axioms.EF C D A B F C B E) /\ ((euclidean__axioms.EF C D A B E B C F) /\ ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E)))))) as H102.
------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------ destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.EF C D A B F C B E) /\ ((euclidean__axioms.EF C D A B E B C F) /\ ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E))))) as H104.
------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.EF C D A B E B C F) /\ ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E)))) as H106.
-------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.EF C D A B C B E F) /\ ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E))) as H108.
--------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.EF C D A B F E B C) /\ (euclidean__axioms.EF C D A B B C F E)) as H110.
---------------------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H106.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F C D A B) as H100.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H100.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (C) (D) (A) (B) (E) (B) (C) (F) H99).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A B C D) as H101.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F A B C D) /\ ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D))))))) as H101.
------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation (E) (B) (C) (F) (C) (D) (A) (B) H100).
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.EF E B C F D A B C) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F A B C D) /\ ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D))))))) as H102.
------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F A B C D) /\ ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D)))))) as H104.
-------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.EF E B C F A B C D) /\ ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D))))) as H106.
--------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.EF E B C F D C B A) /\ ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D)))) as H108.
---------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.EF E B C F B C D A) /\ ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D))) as H110.
----------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.EF E B C F A D C B) /\ (euclidean__axioms.EF E B C F C B A D)) as H112.
------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
exact H106.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H102.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H102.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (E) (B) (C) (F) (A) (B) (C) (D) H101).
------------------------------------------------------------------------------------------------ exact H102.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F D C B E A) as H70.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H70.
----------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H72.
------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* Cut *) ((euclidean__axioms.ET F D C A B E) /\ ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))))) as H74.
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (D) (C) (E) (A) (B) H65).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F D C A B E) /\ ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))))) as H75.
-------------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.ET F D C E B A) /\ ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A)))) as H77.
--------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.ET F D C A E B) /\ ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A))) as H79.
---------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.ET F D C B A E) /\ (euclidean__axioms.ET F D C B E A)) as H81.
----------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H82.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E A F D C) as H71.
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H71.
------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H73.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H75.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (F) (D) (C) (B) (E) (A) H70).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E A C D F) as H72.
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H72.
------------------------------------------------------------------------- exact H58.
------------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H74.
-------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* Cut *) ((euclidean__axioms.ET B E A D C F) /\ ((euclidean__axioms.ET B E A F C D) /\ ((euclidean__axioms.ET B E A D F C) /\ ((euclidean__axioms.ET B E A C D F) /\ (euclidean__axioms.ET B E A C F D))))) as H76.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (B) (E) (A) (F) (D) (C) H71).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET B E A D C F) /\ ((euclidean__axioms.ET B E A F C D) /\ ((euclidean__axioms.ET B E A D F C) /\ ((euclidean__axioms.ET B E A C D F) /\ (euclidean__axioms.ET B E A C F D))))) as H77.
---------------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.ET B E A F C D) /\ ((euclidean__axioms.ET B E A D F C) /\ ((euclidean__axioms.ET B E A C D F) /\ (euclidean__axioms.ET B E A C F D)))) as H79.
----------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.ET B E A D F C) /\ ((euclidean__axioms.ET B E A C D F) /\ (euclidean__axioms.ET B E A C F D))) as H81.
------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.ET B E A C D F) /\ (euclidean__axioms.ET B E A C F D)) as H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H83.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol D B C) as H73.
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H73.
-------------------------------------------------------------------------- exact H58.
-------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H75.
--------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H77.
---------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H21).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H78.
----------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H80.
------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H82.
------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H82.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B C) as H74.
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H74.
--------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H76.
---------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H78.
----------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> (euclidean__axioms.nCol E B C))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
------------------------------------------------------------------------------intro H79.
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
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> (euclidean__axioms.nCol E0 B C))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
-------------------------------------------------------------------------------intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
assert (* Cut *) (e = e) as H183.
-------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------- exact H179.

------------------------------------------------------------------------------- exact H27.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- exact H0.
------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------- exact H6.
------------------------------------------------------------------------------- exact H7.
------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------- exact H9.
------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------- exact H13.
------------------------------------------------------------------------------- exact H15.
------------------------------------------------------------------------------- exact H19.
------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------------- exact H26.
------------------------------------------------------------------------------- exact H28.
------------------------------------------------------------------------------- exact H29.
------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------- exact H120.

------------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------------ exact H.
------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------------ exact H21.
------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------ exact H5.
------------------------------------------------------------------------------ exact H8.
------------------------------------------------------------------------------ exact H10.
------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------ exact H12.
------------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------ exact H33.
------------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------------ exact H35.
------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------ exact H41.
------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------ exact H47.
------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------ exact H57.
------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------ exact H63.
------------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------------ exact H65.
------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------ exact H73.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E C) as H75.
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H75.
---------------------------------------------------------------------------- exact H58.
---------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H77.
----------------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* Cut *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))))) as H79.
------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (E) (B) (C) H74).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))))) as H80.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E)))) as H82.
-------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E))) as H84.
--------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.nCol E C B) /\ (euclidean__axioms.nCol C B E)) as H86.
---------------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H80.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B E C) as H76.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H76.
----------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E C B E C) as H77.
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H77.
------------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H79.
------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H81.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------- apply (@lemma__ETreflexive.lemma__ETreflexive (B) (E) (C) H76).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E C C E B) as H78.
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H78.
------------------------------------------------------------------------------- exact H58.
------------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H80.
-------------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* Cut *) ((euclidean__axioms.ET B E C E C B) /\ ((euclidean__axioms.ET B E C B C E) /\ ((euclidean__axioms.ET B E C E B C) /\ ((euclidean__axioms.ET B E C C E B) /\ (euclidean__axioms.ET B E C C B E))))) as H82.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (B) (E) (C) (B) (E) (C) H77).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET B E C E C B) /\ ((euclidean__axioms.ET B E C B C E) /\ ((euclidean__axioms.ET B E C E B C) /\ ((euclidean__axioms.ET B E C C E B) /\ (euclidean__axioms.ET B E C C B E))))) as H83.
---------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.ET B E C B C E) /\ ((euclidean__axioms.ET B E C E B C) /\ ((euclidean__axioms.ET B E C C E B) /\ (euclidean__axioms.ET B E C C B E)))) as H85.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.ET B E C E B C) /\ ((euclidean__axioms.ET B E C C E B) /\ (euclidean__axioms.ET B E C C B E))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.ET B E C C E B) /\ (euclidean__axioms.ET B E C C B E)) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H89.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET B E C C D B) as H79.
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H79.
-------------------------------------------------------------------------------- exact H58.
-------------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H81.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H83.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> (euclidean__axioms.ET B E C C D0 B))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
-----------------------------------------------------------------------------------intro H84.
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
intro H125.
intro H126.
intro H127.
intro H128.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> (euclidean__axioms.ET B E0 C C E0 B)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
------------------------------------------------------------------------------------intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
assert (* Cut *) (e = e) as H193.
------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------- exact H192.

------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------ exact H7.
------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------ exact H28.
------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------ exact H78.

----------------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------- exact H31.
----------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------------- exact H49.
----------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------- exact H57.
----------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------- exact H73.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B C E) as H80.
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H80.
--------------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H84.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> (euclidean__defs.PG A B C E)))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
------------------------------------------------------------------------------------intro H85.
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
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> (euclidean__defs.PG A B C E0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
-------------------------------------------------------------------------------------intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
assert (* Cut *) (e = e) as H196.
-------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------- exact H131.

------------------------------------------------------------------------------------- exact H27.
------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------- exact H0.
------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------------- exact H6.
------------------------------------------------------------------------------------- exact H7.
------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------- exact H9.
------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------- exact H13.
------------------------------------------------------------------------------------- exact H15.
------------------------------------------------------------------------------------- exact H19.
------------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------------------- exact H26.
------------------------------------------------------------------------------------- exact H28.
------------------------------------------------------------------------------------- exact H29.
------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------- exact H130.

------------------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------------------ exact H.
------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------------------ exact H21.
------------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------------ exact H5.
------------------------------------------------------------------------------------ exact H8.
------------------------------------------------------------------------------------ exact H10.
------------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------------ exact H12.
------------------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------------ exact H33.
------------------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------------------ exact H35.
------------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------------ exact H41.
------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ exact H47.
------------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------------ exact H57.
------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------------ exact H63.
------------------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------------------ exact H65.
------------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------------------ exact H79.
-------------------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M E)) as H81.
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H81.
---------------------------------------------------------------------------------- exact H58.
---------------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H83.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H85.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (B) (C) (E) H80).
--------------------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M E))) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [M H82].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M E)) as H83.
----------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Cong F C E B) /\ ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E))) as H85.
------------------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.CongA D F C A E B) /\ (euclidean__defs.CongA D C F A B E)) as H87.
------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* Cut *) (euclidean__axioms.BetS E M B) as H89.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H89.
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (E) H84).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E M B) as H90.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H90.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H89.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E M) as H91.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M E B) /\ ((euclidean__axioms.Col M B E) /\ ((euclidean__axioms.Col B E M) /\ ((euclidean__axioms.Col E B M) /\ (euclidean__axioms.Col B M E))))) as H91.
----------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (M) (B) H90).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M E B) /\ ((euclidean__axioms.Col M B E) /\ ((euclidean__axioms.Col B E M) /\ ((euclidean__axioms.Col E B M) /\ (euclidean__axioms.Col B M E))))) as H92.
------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col M B E) /\ ((euclidean__axioms.Col B E M) /\ ((euclidean__axioms.Col E B M) /\ (euclidean__axioms.Col B M E)))) as H94.
------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col B E M) /\ ((euclidean__axioms.Col E B M) /\ (euclidean__axioms.Col B M E))) as H96.
-------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E B M) /\ (euclidean__axioms.Col B M E)) as H98.
--------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H96.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A E B C) as H92.
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par A B C E) /\ (euclidean__defs.Par A E B C)) as H92.
------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H94.
------------------------------------------------------------------------------------------- exact H0.
------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H96.
-------------------------------------------------------------------------------------------- exact H.
-------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H93.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H93.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol A E C)))) as H93.
------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (E) (B) (C) H92).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol A E C)))) as H94.
-------------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol A E C))) as H96.
--------------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol A E C)) as H98.
---------------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H94.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B E A) as H94.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))))) as H94.
-------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (B) H93).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))))) as H95.
--------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A)))) as H97.
---------------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A))) as H99.
----------------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ (euclidean__axioms.nCol B E A)) as H101.
------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------ destruct H101 as [H101 H102].
exact H102.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A B E C) as H95.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H95.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------- exists M.
split.
---------------------------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG D B C F) as H96.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H96.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> (euclidean__defs.PG D0 B C F)))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
-----------------------------------------------------------------------------------------------intro H97.
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
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.BetS B M E0) -> ((euclidean__axioms.BetS E0 M B) -> ((euclidean__axioms.Col E0 M B) -> ((euclidean__axioms.Col B E0 M) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__axioms.nCol B E0 A) -> ((euclidean__axioms.TS A B E0 C) -> (euclidean__defs.PG E0 B C F)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
------------------------------------------------------------------------------------------------intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
intro H205.
intro H206.
intro H207.
intro H208.
intro H209.
intro H210.
intro H211.
intro H212.
intro H213.
intro H214.
intro H215.
intro H216.
assert (* Cut *) (e = e) as H217.
------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------- exact H144.

------------------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------------------ exact H7.
------------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------------------ exact H28.
------------------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------ exact H95.

----------------------------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------------------- exact H31.
----------------------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------------------------- exact H49.
----------------------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------- exact H57.
----------------------------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C D F) as H97.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D F C) /\ ((euclidean__axioms.nCol D C F) /\ ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F C D) /\ (euclidean__axioms.nCol C D F))))) as H97.
----------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (F) (D) (C) H63).
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D F C) /\ ((euclidean__axioms.nCol D C F) /\ ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F C D) /\ (euclidean__axioms.nCol C D F))))) as H98.
------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.nCol D C F) /\ ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F C D) /\ (euclidean__axioms.nCol C D F)))) as H100.
------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol C F D) /\ ((euclidean__axioms.nCol F C D) /\ (euclidean__axioms.nCol C D F))) as H102.
-------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.nCol F C D) /\ (euclidean__axioms.nCol C D F)) as H104.
--------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H105.
---------------------------------------------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS D m C) /\ (euclidean__axioms.BetS B m F)) as H98.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H98.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (D) (B) (C) (F) H96).
----------------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS D m C) /\ (euclidean__axioms.BetS B m F))) as H99.
------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------ destruct H99 as [m H99].
assert (* AndElim *) ((euclidean__axioms.BetS D m C) /\ (euclidean__axioms.BetS B m F)) as H100.
------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* Cut *) (euclidean__axioms.BetS F m B) as H102.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H102.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (m) (F) H101).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D m C) as H103.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H103.
---------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H100.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D m) as H104.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m D C) /\ ((euclidean__axioms.Col m C D) /\ ((euclidean__axioms.Col C D m) /\ ((euclidean__axioms.Col D C m) /\ (euclidean__axioms.Col C m D))))) as H104.
----------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (m) (C) H103).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m D C) /\ ((euclidean__axioms.Col m C D) /\ ((euclidean__axioms.Col C D m) /\ ((euclidean__axioms.Col D C m) /\ (euclidean__axioms.Col C m D))))) as H105.
------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col m C D) /\ ((euclidean__axioms.Col C D m) /\ ((euclidean__axioms.Col D C m) /\ (euclidean__axioms.Col C m D)))) as H107.
------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col C D m) /\ ((euclidean__axioms.Col D C m) /\ (euclidean__axioms.Col C m D))) as H109.
-------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col D C m) /\ (euclidean__axioms.Col C m D)) as H111.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H109.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS F C D B) as H105.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H105.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------ exists m.
split.
------------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS A J C) /\ (euclidean__axioms.BetS B J D)) as H106.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H106.
------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (B) (C) (D) H).
------------------------------------------------------------------------------------------------------ assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS A J C) /\ (euclidean__axioms.BetS B J D))) as H107.
------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------- destruct H107 as [J H107].
assert (* AndElim *) ((euclidean__axioms.BetS A J C) /\ (euclidean__axioms.BetS B J D)) as H108.
-------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* Cut *) (euclidean__axioms.BetS B J E) as H110.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H110.
---------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> ((euclidean__defs.PG D0 B C F) -> ((euclidean__axioms.nCol C D0 F) -> ((euclidean__axioms.BetS D0 m C) -> ((euclidean__axioms.Col D0 m C) -> ((euclidean__axioms.Col C D0 m) -> ((euclidean__axioms.TS F C D0 B) -> ((euclidean__axioms.BetS B J D0) -> (euclidean__axioms.BetS B J E))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
-----------------------------------------------------------------------------------------------------------intro H111.
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
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.BetS B M E0) -> ((euclidean__axioms.BetS E0 M B) -> ((euclidean__axioms.Col E0 M B) -> ((euclidean__axioms.Col B E0 M) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__axioms.nCol B E0 A) -> ((euclidean__axioms.TS A B E0 C) -> ((euclidean__axioms.nCol C E0 F) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS E0 m C) -> ((euclidean__axioms.TS F C E0 B) -> ((euclidean__axioms.Col C E0 m) -> ((euclidean__axioms.Col E0 m C) -> ((euclidean__axioms.BetS B J E0) -> (euclidean__axioms.BetS B J E0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
------------------------------------------------------------------------------------------------------------intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
intro H205.
intro H206.
intro H207.
intro H208.
intro H209.
intro H210.
intro H211.
intro H212.
intro H213.
intro H214.
intro H215.
intro H216.
intro H217.
intro H218.
intro H219.
intro H220.
intro H221.
intro H222.
intro H223.
intro H224.
intro H225.
intro H226.
intro H227.
intro H228.
intro H229.
intro H230.
intro H231.
intro H232.
intro H233.
intro H234.
intro H235.
intro H236.
intro H237.
intro H238.
intro H239.
intro H240.
intro H241.
intro H242.
intro H243.
intro H244.
assert (* Cut *) (e = e) as H245.
------------------------------------------------------------------------------------------------------------- exact H187.
------------------------------------------------------------------------------------------------------------- exact H244.

------------------------------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------------------------------ exact H7.
------------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------------------------------ exact H28.
------------------------------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------ exact H145.
------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------ exact H154.
------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------ exact H157.
------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------ exact H160.
------------------------------------------------------------------------------------------------------------ exact H163.

----------------------------------------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------------------------------- exact H31.
----------------------------------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------------------------------------- exact H49.
----------------------------------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------------------- exact H57.
----------------------------------------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (j: euclidean__axioms.Point), (euclidean__axioms.BetS E j C) /\ (euclidean__axioms.BetS B j F)) as H111.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H111.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (E) (B) (C) (F) H0).
---------------------------------------------------------------------------------------------------------- assert (exists j: euclidean__axioms.Point, ((euclidean__axioms.BetS E j C) /\ (euclidean__axioms.BetS B j F))) as H112.
----------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------- destruct H112 as [j H112].
assert (* AndElim *) ((euclidean__axioms.BetS E j C) /\ (euclidean__axioms.BetS B j F)) as H113.
------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* Cut *) (euclidean__axioms.BetS D j C) as H115.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H115.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> ((euclidean__defs.PG D0 B C F) -> ((euclidean__axioms.nCol C D0 F) -> ((euclidean__axioms.BetS D0 m C) -> ((euclidean__axioms.Col D0 m C) -> ((euclidean__axioms.Col C D0 m) -> ((euclidean__axioms.TS F C D0 B) -> ((euclidean__axioms.BetS B J D0) -> (euclidean__axioms.BetS D0 j C))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
---------------------------------------------------------------------------------------------------------------intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.BetS B M E0) -> ((euclidean__axioms.BetS E0 M B) -> ((euclidean__axioms.Col E0 M B) -> ((euclidean__axioms.Col B E0 M) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__axioms.nCol B E0 A) -> ((euclidean__axioms.TS A B E0 C) -> ((euclidean__axioms.nCol C E0 F) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS E0 m C) -> ((euclidean__axioms.TS F C E0 B) -> ((euclidean__axioms.Col C E0 m) -> ((euclidean__axioms.Col E0 m C) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS E0 j C) -> (euclidean__axioms.BetS E0 j C))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
----------------------------------------------------------------------------------------------------------------intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
intro H205.
intro H206.
intro H207.
intro H208.
intro H209.
intro H210.
intro H211.
intro H212.
intro H213.
intro H214.
intro H215.
intro H216.
intro H217.
intro H218.
intro H219.
intro H220.
intro H221.
intro H222.
intro H223.
intro H224.
intro H225.
intro H226.
intro H227.
intro H228.
intro H229.
intro H230.
intro H231.
intro H232.
intro H233.
intro H234.
intro H235.
intro H236.
intro H237.
intro H238.
intro H239.
intro H240.
intro H241.
intro H242.
intro H243.
intro H244.
intro H245.
intro H246.
intro H247.
intro H248.
intro H249.
intro H250.
intro H251.
assert (* Cut *) (e = e) as H252.
----------------------------------------------------------------------------------------------------------------- exact H192.
----------------------------------------------------------------------------------------------------------------- exact H251.

---------------------------------------------------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------- exact H0.
---------------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------------- exact H6.
---------------------------------------------------------------------------------------------------------------- exact H7.
---------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------- exact H9.
---------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------- exact H13.
---------------------------------------------------------------------------------------------------------------- exact H15.
---------------------------------------------------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------------------------------------------------- exact H25.
---------------------------------------------------------------------------------------------------------------- exact H26.
---------------------------------------------------------------------------------------------------------------- exact H28.
---------------------------------------------------------------------------------------------------------------- exact H29.
---------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------- exact H131.
---------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------- exact H147.
---------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------- exact H145.
---------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------- exact H142.
---------------------------------------------------------------------------------------------------------------- exact H141.
---------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------------------------------------------- exact H156.
---------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------- exact H153.
---------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------- exact H151.
---------------------------------------------------------------------------------------------------------------- exact H150.
---------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------- exact H159.
---------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------- exact H157.
---------------------------------------------------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------------------------------- exact H163.
---------------------------------------------------------------------------------------------------------------- exact H162.
---------------------------------------------------------------------------------------------------------------- exact H164.
---------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------- exact H166.
---------------------------------------------------------------------------------------------------------------- exact H165.
---------------------------------------------------------------------------------------------------------------- exact H168.
---------------------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------------------- exact H113.

--------------------------------------------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------------- exact H20.
--------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------------------------------------------------- exact H5.
--------------------------------------------------------------------------------------------------------------- exact H8.
--------------------------------------------------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------------------------------------------------- exact H11.
--------------------------------------------------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------------------------------------------- exact H31.
--------------------------------------------------------------------------------------------------------------- exact H32.
--------------------------------------------------------------------------------------------------------------- exact H33.
--------------------------------------------------------------------------------------------------------------- exact H34.
--------------------------------------------------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------------------------------------------------- exact H36.
--------------------------------------------------------------------------------------------------------------- exact H40.
--------------------------------------------------------------------------------------------------------------- exact H41.
--------------------------------------------------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------------- exact H47.
--------------------------------------------------------------------------------------------------------------- exact H48.
--------------------------------------------------------------------------------------------------------------- exact H49.
--------------------------------------------------------------------------------------------------------------- exact H50.
--------------------------------------------------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------------------------------------------- exact H56.
--------------------------------------------------------------------------------------------------------------- exact H57.
--------------------------------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------------------------------- exact H59.
--------------------------------------------------------------------------------------------------------------- exact H60.
--------------------------------------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------------------------------------- exact H62.
--------------------------------------------------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C j D) as H116.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H116.
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (j) (C) H115).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F j B) as H117.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H117.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (j) (F) H114).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B A E C C F D B) as H118.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H118.
----------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 (B) (E) (A) (C) (J) (C) (D) (F) (B) (j) (H72) (H79) (H108)).
------------------------------------------------------------------------------------------------------------------left.
exact H110.

------------------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------------------left.
exact H116.

---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B A E C D B C F) as H119.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B A E C F D B C) /\ ((euclidean__axioms.EF B A E C B D F C) /\ ((euclidean__axioms.EF B A E C D B C F) /\ ((euclidean__axioms.EF B A E C F C B D) /\ ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F))))))) as H119.
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation (B) (A) (E) (C) (C) (F) (D) (B) H118).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.EF B A E C F D B C) /\ ((euclidean__axioms.EF B A E C B D F C) /\ ((euclidean__axioms.EF B A E C D B C F) /\ ((euclidean__axioms.EF B A E C F C B D) /\ ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F))))))) as H120.
------------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.EF B A E C B D F C) /\ ((euclidean__axioms.EF B A E C D B C F) /\ ((euclidean__axioms.EF B A E C F C B D) /\ ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F)))))) as H122.
-------------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.EF B A E C D B C F) /\ ((euclidean__axioms.EF B A E C F C B D) /\ ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F))))) as H124.
--------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.EF B A E C F C B D) /\ ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F)))) as H126.
---------------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.EF B A E C B C F D) /\ ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F))) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.EF B A E C D F C B) /\ (euclidean__axioms.EF B A E C C B D F)) as H130.
------------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
exact H124.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B A E C E B C F) as H120.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H120.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> ((euclidean__defs.PG D0 B C F) -> ((euclidean__axioms.nCol C D0 F) -> ((euclidean__axioms.BetS D0 m C) -> ((euclidean__axioms.Col D0 m C) -> ((euclidean__axioms.Col C D0 m) -> ((euclidean__axioms.TS F C D0 B) -> ((euclidean__axioms.BetS B J D0) -> ((euclidean__axioms.BetS D0 j C) -> ((euclidean__axioms.BetS C j D0) -> ((euclidean__axioms.EF B A E C C F D0 B) -> ((euclidean__axioms.EF B A E C D0 B C F) -> (euclidean__axioms.EF B A E C E B C F))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
--------------------------------------------------------------------------------------------------------------------intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.BetS B M E0) -> ((euclidean__axioms.BetS E0 M B) -> ((euclidean__axioms.Col E0 M B) -> ((euclidean__axioms.Col B E0 M) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__axioms.nCol B E0 A) -> ((euclidean__axioms.TS A B E0 C) -> ((euclidean__axioms.nCol C E0 F) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS E0 m C) -> ((euclidean__axioms.TS F C E0 B) -> ((euclidean__axioms.Col C E0 m) -> ((euclidean__axioms.Col E0 m C) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS E0 j C) -> ((euclidean__axioms.BetS C j E0) -> ((euclidean__axioms.BetS E0 j C) -> ((euclidean__axioms.EF B A E0 C E0 B C F) -> ((euclidean__axioms.EF B A E0 C C F E0 B) -> (euclidean__axioms.EF B A E0 C E0 B C F))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
---------------------------------------------------------------------------------------------------------------------intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
intro H205.
intro H206.
intro H207.
intro H208.
intro H209.
intro H210.
intro H211.
intro H212.
intro H213.
intro H214.
intro H215.
intro H216.
intro H217.
intro H218.
intro H219.
intro H220.
intro H221.
intro H222.
intro H223.
intro H224.
intro H225.
intro H226.
intro H227.
intro H228.
intro H229.
intro H230.
intro H231.
intro H232.
intro H233.
intro H234.
intro H235.
intro H236.
intro H237.
intro H238.
intro H239.
intro H240.
intro H241.
intro H242.
intro H243.
intro H244.
intro H245.
intro H246.
intro H247.
intro H248.
intro H249.
intro H250.
intro H251.
intro H252.
intro H253.
intro H254.
intro H255.
intro H256.
intro H257.
intro H258.
intro H259.
intro H260.
intro H261.
intro H262.
intro H263.
intro H264.
assert (* Cut *) (e = e) as H265.
---------------------------------------------------------------------------------------------------------------------- exact H201.
---------------------------------------------------------------------------------------------------------------------- exact H263.

--------------------------------------------------------------------------------------------------------------------- exact H27.
--------------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------- exact H6.
--------------------------------------------------------------------------------------------------------------------- exact H7.
--------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------- exact H9.
--------------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------- exact H13.
--------------------------------------------------------------------------------------------------------------------- exact H15.
--------------------------------------------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------------------------------------------- exact H24.
--------------------------------------------------------------------------------------------------------------------- exact H25.
--------------------------------------------------------------------------------------------------------------------- exact H26.
--------------------------------------------------------------------------------------------------------------------- exact H28.
--------------------------------------------------------------------------------------------------------------------- exact H29.
--------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------- exact H152.
--------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------- exact H150.
--------------------------------------------------------------------------------------------------------------------- exact H149.
--------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------- exact H160.
--------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------- exact H157.
--------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------- exact H155.
--------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------- exact H165.
--------------------------------------------------------------------------------------------------------------------- exact H164.
--------------------------------------------------------------------------------------------------------------------- exact H163.
--------------------------------------------------------------------------------------------------------------------- exact H162.
--------------------------------------------------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------------------------------------------------- exact H166.
--------------------------------------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------------------------------------- exact H168.
--------------------------------------------------------------------------------------------------------------------- exact H167.
--------------------------------------------------------------------------------------------------------------------- exact H169.
--------------------------------------------------------------------------------------------------------------------- exact H172.
--------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------- exact H173.
--------------------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------- exact H174.
--------------------------------------------------------------------------------------------------------------------- exact H177.
--------------------------------------------------------------------------------------------------------------------- exact H176.

-------------------------------------------------------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------------------------------------------------------- exact H.
-------------------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------------------- exact H20.
-------------------------------------------------------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------------------------------------------------------- exact H4.
-------------------------------------------------------------------------------------------------------------------- exact H5.
-------------------------------------------------------------------------------------------------------------------- exact H8.
-------------------------------------------------------------------------------------------------------------------- exact H10.
-------------------------------------------------------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------------------------------------------------------- exact H12.
-------------------------------------------------------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------------------------------------------------------- exact H31.
-------------------------------------------------------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------------------------------------------------------- exact H33.
-------------------------------------------------------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------------------------------------------------------- exact H42.
-------------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------------------------------------------------------- exact H49.
-------------------------------------------------------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------------------------------------------------------- exact H51.
-------------------------------------------------------------------------------------------------------------------- exact H52.
-------------------------------------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------------------------------------------------------- exact H56.
-------------------------------------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------------------------------------------------------- exact H62.
-------------------------------------------------------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF E B C F B A E C) as H121.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H121.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (B) (A) (E) (C) (E) (B) (C) (F) H120).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A B C E) as H122.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF E B C F A E C B) /\ ((euclidean__axioms.EF E B C F C E A B) /\ ((euclidean__axioms.EF E B C F E C B A) /\ ((euclidean__axioms.EF E B C F A B C E) /\ ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A))))))) as H122.
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (E) (B) (C) (F) (B) (A) (E) (C) H121).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF E B C F A E C B) /\ ((euclidean__axioms.EF E B C F C E A B) /\ ((euclidean__axioms.EF E B C F E C B A) /\ ((euclidean__axioms.EF E B C F A B C E) /\ ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A))))))) as H123.
---------------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.EF E B C F C E A B) /\ ((euclidean__axioms.EF E B C F E C B A) /\ ((euclidean__axioms.EF E B C F A B C E) /\ ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A)))))) as H125.
----------------------------------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.EF E B C F E C B A) /\ ((euclidean__axioms.EF E B C F A B C E) /\ ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A))))) as H127.
------------------------------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------------------------------ destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.EF E B C F A B C E) /\ ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A)))) as H129.
------------------------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.EF E B C F C B A E) /\ ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A))) as H131.
-------------------------------------------------------------------------------------------------------------------------- exact H130.
-------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.EF E B C F E A B C) /\ (euclidean__axioms.EF E B C F B C E A)) as H133.
--------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H129.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A B C D) as H123.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H123.
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
---------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.BetS A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.Cong A D0 F E) -> ((euclidean__axioms.Cong A D0 A D0) -> ((euclidean__defs.Lt A D0 A F) -> ((euclidean__defs.Par D0 C A B) -> ((euclidean__axioms.BetS F D0 A) -> ((euclidean__defs.TP A D0 B C) -> ((euclidean__defs.OS B C A D0) -> ((euclidean__defs.OS C B D0 A) -> ((euclidean__defs.CongA F D0 C D0 A B) -> ((D0 = D0) -> ((euclidean__axioms.nCol A D0 C) -> ((~(A = D0)) -> ((euclidean__axioms.neq A D0) -> (((euclidean__axioms.BetS A D0 E) \/ ((euclidean__axioms.BetS A E D0) \/ (D0 = E))) -> ((euclidean__defs.Out A D0 E) -> ((euclidean__axioms.nCol A D0 B) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__defs.CongA D0 A B D0 A B) -> ((euclidean__defs.CongA D0 A B E A B) -> ((euclidean__defs.CongA F D0 C E A B) -> ((euclidean__axioms.Cong A B D0 C) -> ((euclidean__axioms.Cong D0 E E D0) -> ((euclidean__axioms.Cong A E D0 F) -> ((euclidean__axioms.Cong D0 F A E) -> ((euclidean__axioms.Cong D0 C A B) -> ((euclidean__defs.CongA D0 F C A E B) -> ((euclidean__defs.CongA D0 C F A B E) -> ((euclidean__axioms.Cong F D0 E A) -> ((euclidean__defs.CongA A B E D0 C F) -> ((euclidean__axioms.nCol D0 C F) -> ((euclidean__axioms.nCol F D0 C) -> ((euclidean__axioms.Triangle F D0 C) -> ((euclidean__axioms.Cong__3 F D0 C E A B) -> ((euclidean__axioms.ET F D0 C E A B) -> ((euclidean__axioms.ET F D0 C B E A) -> ((euclidean__axioms.ET B E A F D0 C) -> ((euclidean__axioms.ET B E A C D0 F) -> ((euclidean__axioms.nCol D0 B C) -> ((euclidean__axioms.ET B E C C D0 B) -> ((euclidean__defs.PG D0 B C F) -> ((euclidean__axioms.nCol C D0 F) -> ((euclidean__axioms.BetS D0 m C) -> ((euclidean__axioms.Col D0 m C) -> ((euclidean__axioms.Col C D0 m) -> ((euclidean__axioms.TS F C D0 B) -> ((euclidean__axioms.BetS B J D0) -> ((euclidean__axioms.BetS D0 j C) -> ((euclidean__axioms.BetS C j D0) -> ((euclidean__axioms.EF B A E C C F D0 B) -> ((euclidean__axioms.EF B A E C D0 B C F) -> (euclidean__axioms.EF E B C F A B C D0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := D).
-----------------------------------------------------------------------------------------------------------------------intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
apply (@eq__ind euclidean__axioms.Point e (fun E0: euclidean__axioms.Point => (euclidean__defs.PG A B C E0) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__axioms.Cong A E0 B C) -> ((euclidean__defs.Par A B E0 C) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__defs.Par A B C E0) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 F F E0) -> ((euclidean__defs.Lt A E0 A F) -> ((euclidean__axioms.Cong A E0 A E0) -> ((euclidean__axioms.Cong A E0 F E0) -> ((euclidean__defs.Lt F E0 A F) -> ((euclidean__defs.Lt F E0 F A) -> ((euclidean__axioms.Cong F e F E0) -> ((euclidean__axioms.BetS A E0 F) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Out F A E0) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__axioms.BetS A E0 F) -> ((E0 = E0) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.OS C B E0 A) -> ((euclidean__defs.OS B C A E0) -> ((euclidean__defs.TP A E0 B C) -> ((euclidean__axioms.BetS F E0 A) -> ((euclidean__defs.Par E0 C A B) -> ((euclidean__axioms.neq A E0) -> ((~(A = E0)) -> ((euclidean__axioms.nCol A E0 C) -> ((euclidean__axioms.Cong E0 C A B) -> ((euclidean__axioms.Cong E0 F A E0) -> ((euclidean__axioms.Cong A E0 E0 F) -> ((euclidean__axioms.Cong E0 E0 E0 E0) -> ((euclidean__axioms.Cong A B E0 C) -> ((euclidean__defs.CongA F E0 C E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__defs.CongA E0 A B E0 A B) -> ((euclidean__axioms.nCol E0 A B) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__defs.Out A E0 E0) -> (((euclidean__axioms.BetS A E0 E0) \/ ((euclidean__axioms.BetS A E0 E0) \/ (E0 = E0))) -> ((euclidean__axioms.Cong F C E0 B) -> ((euclidean__axioms.ET F E0 C E0 A B) -> ((euclidean__axioms.Cong__3 F E0 C E0 A B) -> ((euclidean__axioms.Triangle F E0 C) -> ((euclidean__axioms.nCol F E0 C) -> ((euclidean__axioms.nCol E0 C F) -> ((euclidean__defs.CongA A B E0 E0 C F) -> ((euclidean__axioms.Cong F E0 E0 A) -> ((euclidean__defs.CongA E0 C F A B E0) -> ((euclidean__defs.CongA E0 F C A E0 B) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.ET B E0 A C E0 F) -> ((euclidean__axioms.ET B E0 A F E0 C) -> ((euclidean__axioms.ET F E0 C B E0 A) -> ((euclidean__axioms.nCol E0 B C) -> ((euclidean__axioms.nCol B E0 C) -> ((euclidean__axioms.Triangle B E0 C) -> ((euclidean__axioms.ET B E0 C B E0 C) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__axioms.ET B E0 C C E0 B) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.BetS B M E0) -> ((euclidean__axioms.BetS E0 M B) -> ((euclidean__axioms.Col E0 M B) -> ((euclidean__axioms.Col B E0 M) -> ((euclidean__defs.Par A E0 B C) -> ((euclidean__axioms.nCol A E0 B) -> ((euclidean__axioms.nCol B E0 A) -> ((euclidean__axioms.TS A B E0 C) -> ((euclidean__axioms.nCol C E0 F) -> ((euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.BetS E0 m C) -> ((euclidean__axioms.TS F C E0 B) -> ((euclidean__axioms.Col C E0 m) -> ((euclidean__axioms.Col E0 m C) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS B J E0) -> ((euclidean__axioms.BetS E0 j C) -> ((euclidean__axioms.BetS C j E0) -> ((euclidean__axioms.BetS E0 j C) -> ((euclidean__axioms.EF B A E0 C E0 B C F) -> ((euclidean__axioms.EF B A E0 C C F E0 B) -> ((euclidean__axioms.EF B A E0 C E0 B C F) -> ((euclidean__axioms.EF E0 B C F B A E0 C) -> ((euclidean__axioms.EF E0 B C F A B C E0) -> (euclidean__axioms.EF E0 B C F A B C E0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (y := E).
------------------------------------------------------------------------------------------------------------------------intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
intro H205.
intro H206.
intro H207.
intro H208.
intro H209.
intro H210.
intro H211.
intro H212.
intro H213.
intro H214.
intro H215.
intro H216.
intro H217.
intro H218.
intro H219.
intro H220.
intro H221.
intro H222.
intro H223.
intro H224.
intro H225.
intro H226.
intro H227.
intro H228.
intro H229.
intro H230.
intro H231.
intro H232.
intro H233.
intro H234.
intro H235.
intro H236.
intro H237.
intro H238.
intro H239.
intro H240.
intro H241.
intro H242.
intro H243.
intro H244.
intro H245.
intro H246.
intro H247.
intro H248.
intro H249.
intro H250.
intro H251.
intro H252.
intro H253.
intro H254.
intro H255.
intro H256.
intro H257.
intro H258.
intro H259.
intro H260.
intro H261.
intro H262.
intro H263.
intro H264.
intro H265.
intro H266.
intro H267.
intro H268.
intro H269.
intro H270.
assert (* Cut *) (e = e) as H271.
------------------------------------------------------------------------------------------------------------------------- exact H204.
------------------------------------------------------------------------------------------------------------------------- exact H270.

------------------------------------------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------------------------------------------ exact H7.
------------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------------------------------------------ exact H25.
------------------------------------------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------------------------------------------ exact H28.
------------------------------------------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------ exact H154.
------------------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------ exact H145.
------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------ exact H163.
------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------ exact H160.
------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------------------ exact H157.
------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------ exact H168.
------------------------------------------------------------------------------------------------------------------------ exact H167.
------------------------------------------------------------------------------------------------------------------------ exact H166.
------------------------------------------------------------------------------------------------------------------------ exact H165.
------------------------------------------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------------------------------ exact H169.
------------------------------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------------------------------ exact H171.
------------------------------------------------------------------------------------------------------------------------ exact H170.
------------------------------------------------------------------------------------------------------------------------ exact H172.
------------------------------------------------------------------------------------------------------------------------ exact H175.
------------------------------------------------------------------------------------------------------------------------ exact H174.
------------------------------------------------------------------------------------------------------------------------ exact H173.
------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------------------ exact H178.
------------------------------------------------------------------------------------------------------------------------ exact H177.
------------------------------------------------------------------------------------------------------------------------ exact H180.
------------------------------------------------------------------------------------------------------------------------ exact H179.
------------------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------------------ exact H122.

----------------------------------------------------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------------------------------------------- exact H20.
----------------------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------------------- exact H4.
----------------------------------------------------------------------------------------------------------------------- exact H5.
----------------------------------------------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------------------------------------------- exact H31.
----------------------------------------------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------------------------------- exact H34.
----------------------------------------------------------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------------------------------------------------- exact H49.
----------------------------------------------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------------------------------- exact H57.
----------------------------------------------------------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H124.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) as H124.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A D E) \/ ((euclidean__axioms.BetS A E D) \/ (D = E))) H46).
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (E) (B) (C) (F) (A) (B) (C) (D) H123).
---------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------- exact H66.
Qed.
