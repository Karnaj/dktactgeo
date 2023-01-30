Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__droppedperpendicularunique.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export lemma__fiveline.
Require Export lemma__inequalitysymmetric.
Require Export lemma__interior5.
Require Export lemma__layoffunique.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__12.
Definition proposition__07 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.Cong C A D A) -> ((euclidean__axioms.Cong C B D B) -> ((euclidean__defs.OS C D A B) -> (C = D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H3.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H3.
-- exact H2.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as __TmpHyp.
--- exact H3.
--- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H4.
---- exact __TmpHyp.
---- destruct H4 as [x H4].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H5.
----- exact H4.
----- destruct H5 as [x0 H5].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C x0 x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))))) as H6.
------ exact H5.
------ destruct H6 as [x1 H6].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS C x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS C x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS C x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H15.
- assert (* Cut *) (exists (F: euclidean__axioms.Point), euclidean__defs.Perp__at C F A B F) as H4.
-- apply (@proposition__12.proposition__12 (A) (B) (C) H3).
-- assert (exists F: euclidean__axioms.Point, (euclidean__defs.Perp__at C F A B F)) as H5.
--- exact H4.
--- destruct H5 as [F H5].
assert (* Cut *) (exists (H6: euclidean__axioms.Point), (euclidean__axioms.Col C F F) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A B H6) /\ (euclidean__defs.Per H6 F C)))) as H6.
---- exact H5.
---- assert (exists H7: euclidean__axioms.Point, ((euclidean__axioms.Col C F F) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A B H7) /\ (euclidean__defs.Per H7 F C))))) as H8.
----- exact H6.
----- destruct H8 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col C F F) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A B H7) /\ (euclidean__defs.Per H7 F C)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A B H7) /\ (euclidean__defs.Per H7 F C))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B H7) /\ (euclidean__defs.Per H7 F C)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* Cut *) (~(C = F)) as H15.
--------- intro H15.
assert (* Cut *) (euclidean__axioms.Col A B C) as H16.
---------- apply (@eq__ind__r euclidean__axioms.Point F (fun C0: euclidean__axioms.Point => (euclidean__axioms.Cong C0 A D A) -> ((euclidean__axioms.Cong C0 B D B) -> ((euclidean__defs.OS C0 D A B) -> ((euclidean__axioms.nCol A B C0) -> ((euclidean__defs.Perp__at C0 F A B F) -> ((euclidean__axioms.Col C0 F F) -> ((euclidean__defs.Per H7 F C0) -> (euclidean__axioms.Col A B C0))))))))) with (x := C).
-----------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
exact H11.

----------- exact H15.
----------- exact H0.
----------- exact H1.
----------- exact H2.
----------- exact H3.
----------- exact H5.
----------- exact H9.
----------- exact H14.
---------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H3) H16).
--------- assert (* Cut *) (euclidean__axioms.neq F C) as H16.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (F) H15).
---------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong F E F C)) as H17.
----------- apply (@lemma__extension.lemma__extension (C) (F) (F) (C) (H15) H16).
----------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong F E F C))) as H18.
------------ exact H17.
------------ destruct H18 as [E H18].
assert (* AndElim *) ((euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong F E F C)) as H19.
------------- exact H18.
------------- destruct H19 as [H19 H20].
assert (* Cut *) (euclidean__axioms.Cong A C A E) as H21.
-------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H21.
--------------- apply (@euclidean__tactics.eq__or__neq (A) F).
--------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H22.
---------------- exact H21.
---------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as __TmpHyp.
----------------- exact H22.
----------------- assert (A = F \/ euclidean__axioms.neq A F) as H23.
------------------ exact __TmpHyp.
------------------ destruct H23 as [H23|H23].
------------------- assert (* Cut *) (euclidean__axioms.Cong A E A C) as H24.
-------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C F A0 B F) -> ((euclidean__axioms.Col A0 B F) -> ((euclidean__axioms.Col A0 B H7) -> (euclidean__axioms.Cong A0 E A0 C))))))))) with (x := A).
---------------------intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
exact H20.

--------------------- exact H23.
--------------------- exact H.
--------------------- exact H0.
--------------------- exact H2.
--------------------- exact H3.
--------------------- exact H5.
--------------------- exact H11.
--------------------- exact H13.
-------------------- assert (* Cut *) (euclidean__axioms.Cong A C A E) as H25.
--------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (E) (C) H24).
--------------------- exact H25.
------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H24.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
-------------------- assert (* Cut *) (euclidean__axioms.Col B A F) as H25.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H25.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H11).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.Col B A H7) as H26.
---------------------- assert (* Cut *) ((euclidean__axioms.Col B A H7) /\ ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))))) as H26.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (H7) H13).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col B A H7) /\ ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A)))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A)) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
exact H27.
---------------------- assert (* Cut *) (euclidean__axioms.Col A F H7) as H27.
----------------------- apply (@euclidean__tactics.not__nCol__Col (A) (F) (H7)).
------------------------intro H27.
apply (@euclidean__tactics.Col__nCol__False (A) (F) (H7) (H27)).
-------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (F) (H7) (H25) (H26) H24).


----------------------- assert (* Cut *) (euclidean__axioms.Col H7 F A) as H28.
------------------------ assert (* Cut *) ((euclidean__axioms.Col F A H7) /\ ((euclidean__axioms.Col F H7 A) /\ ((euclidean__axioms.Col H7 A F) /\ ((euclidean__axioms.Col A H7 F) /\ (euclidean__axioms.Col H7 F A))))) as H28.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (H7) H27).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col F A H7) /\ ((euclidean__axioms.Col F H7 A) /\ ((euclidean__axioms.Col H7 A F) /\ ((euclidean__axioms.Col A H7 F) /\ (euclidean__axioms.Col H7 F A))))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col F H7 A) /\ ((euclidean__axioms.Col H7 A F) /\ ((euclidean__axioms.Col A H7 F) /\ (euclidean__axioms.Col H7 F A)))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col H7 A F) /\ ((euclidean__axioms.Col A H7 F) /\ (euclidean__axioms.Col H7 F A))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A H7 F) /\ (euclidean__axioms.Col H7 F A)) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
exact H36.
------------------------ assert (* Cut *) (euclidean__defs.Per A F C) as H29.
------------------------- apply (@lemma__collinearright.lemma__collinearright (H7) (F) (A) (C) (H14) (H28) H23).
------------------------- assert (* Cut *) (euclidean__defs.Per C F A) as H30.
-------------------------- apply (@lemma__8__2.lemma__8__2 (A) (F) (C) H29).
-------------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C A P A) /\ (euclidean__axioms.neq F A)))) as H31.
--------------------------- exact H30.
--------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C A P A) /\ (euclidean__axioms.neq F A))))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [P H32].
assert (* AndElim *) ((euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C A P A) /\ (euclidean__axioms.neq F A)))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C A P A) /\ (euclidean__axioms.neq F A))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Cong C A P A) /\ (euclidean__axioms.neq F A)) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (euclidean__axioms.Cong F E C F) as H39.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H39.
--------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (E) (F) (C) H20).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F)) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
exact H43.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E P F) as H40.
--------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (E) (C) (F) (P) (F) (H39) H35).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E F P) as H41.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E F F P) /\ ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P))) as H41.
----------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (E) (P) (F) H40).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F F P) /\ ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P)) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
exact H45.
---------------------------------- assert (* Cut *) (E = P) as H42.
----------------------------------- apply (@lemma__extensionunique.lemma__extensionunique (C) (F) (E) (P) (H19) (H33) H41).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A E A) as H43.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point P (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C F E0) -> ((euclidean__axioms.Cong F E0 F C) -> ((euclidean__axioms.Cong F E0 C F) -> ((euclidean__axioms.Cong F E0 P F) -> ((euclidean__axioms.Cong F E0 F P) -> (euclidean__axioms.Cong C A E0 A))))))) with (x := E).
-------------------------------------intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
exact H37.

------------------------------------- exact H42.
------------------------------------- exact H19.
------------------------------------- exact H20.
------------------------------------- exact H39.
------------------------------------- exact H40.
------------------------------------- exact H41.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A C A E) as H44.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C A E) /\ ((euclidean__axioms.Cong A C E A) /\ (euclidean__axioms.Cong C A A E))) as H44.
-------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (E) (A) H43).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C A E) /\ ((euclidean__axioms.Cong A C E A) /\ (euclidean__axioms.Cong C A A E))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Cong A C E A) /\ (euclidean__axioms.Cong C A A E)) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
exact H45.
------------------------------------- exact H44.
-------------- assert (* Cut *) (euclidean__axioms.Cong B C B E) as H22.
--------------- assert (* Cut *) ((B = F) \/ (euclidean__axioms.neq B F)) as H22.
---------------- apply (@euclidean__tactics.eq__or__neq (B) F).
---------------- assert (* Cut *) ((B = F) \/ (euclidean__axioms.neq B F)) as H23.
----------------- exact H22.
----------------- assert (* Cut *) ((B = F) \/ (euclidean__axioms.neq B F)) as __TmpHyp.
------------------ exact H23.
------------------ assert (B = F \/ euclidean__axioms.neq B F) as H24.
------------------- exact __TmpHyp.
------------------- destruct H24 as [H24|H24].
-------------------- assert (* Cut *) (euclidean__axioms.Cong B E B C) as H25.
--------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C F A B0 F) -> ((euclidean__axioms.Col A B0 F) -> ((euclidean__axioms.Col A B0 H7) -> (euclidean__axioms.Cong B0 E B0 C))))))))) with (x := B).
----------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
exact H20.

---------------------- exact H24.
---------------------- exact H.
---------------------- exact H1.
---------------------- exact H2.
---------------------- exact H3.
---------------------- exact H5.
---------------------- exact H11.
---------------------- exact H13.
--------------------- assert (* Cut *) (euclidean__axioms.Cong B C B E) as H26.
---------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (E) (C) H25).
---------------------- exact H26.
-------------------- assert (* Cut *) (euclidean__axioms.Col B A F) as H25.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H25.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H11).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.Col B A H7) as H26.
---------------------- assert (* Cut *) ((euclidean__axioms.Col B A H7) /\ ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))))) as H26.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (H7) H13).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col B A H7) /\ ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B H7 A) /\ ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A)))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col H7 A B) /\ ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A H7 B) /\ (euclidean__axioms.Col H7 B A)) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
exact H27.
---------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H27.
----------------------- assert (* Cut *) ((euclidean__axioms.Col A B H7) /\ ((euclidean__axioms.Col A H7 B) /\ ((euclidean__axioms.Col H7 B A) /\ ((euclidean__axioms.Col B H7 A) /\ (euclidean__axioms.Col H7 A B))))) as H27.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (H7) H26).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col A B H7) /\ ((euclidean__axioms.Col A H7 B) /\ ((euclidean__axioms.Col H7 B A) /\ ((euclidean__axioms.Col B H7 A) /\ (euclidean__axioms.Col H7 A B))))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A H7 B) /\ ((euclidean__axioms.Col H7 B A) /\ ((euclidean__axioms.Col B H7 A) /\ (euclidean__axioms.Col H7 A B)))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col H7 B A) /\ ((euclidean__axioms.Col B H7 A) /\ (euclidean__axioms.Col H7 A B))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B H7 A) /\ (euclidean__axioms.Col H7 A B)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H11.
----------------------- assert (* Cut *) (euclidean__axioms.Col A B H7) as H28.
------------------------ assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H28.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H27).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
exact H13.
------------------------ assert (* Cut *) (euclidean__axioms.Col B F H7) as H29.
------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (H7)).
--------------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (H7) (H29)).
---------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (F) (H7) (H27) (H28) H).


------------------------- assert (* Cut *) (euclidean__axioms.Col H7 F B) as H30.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col F B H7) /\ ((euclidean__axioms.Col F H7 B) /\ ((euclidean__axioms.Col H7 B F) /\ ((euclidean__axioms.Col B H7 F) /\ (euclidean__axioms.Col H7 F B))))) as H30.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (H7) H29).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B H7) /\ ((euclidean__axioms.Col F H7 B) /\ ((euclidean__axioms.Col H7 B F) /\ ((euclidean__axioms.Col B H7 F) /\ (euclidean__axioms.Col H7 F B))))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col F H7 B) /\ ((euclidean__axioms.Col H7 B F) /\ ((euclidean__axioms.Col B H7 F) /\ (euclidean__axioms.Col H7 F B)))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col H7 B F) /\ ((euclidean__axioms.Col B H7 F) /\ (euclidean__axioms.Col H7 F B))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col B H7 F) /\ (euclidean__axioms.Col H7 F B)) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
exact H38.
-------------------------- assert (* Cut *) (euclidean__defs.Per B F C) as H31.
--------------------------- apply (@lemma__collinearright.lemma__collinearright (H7) (F) (B) (C) (H14) (H30) H24).
--------------------------- assert (* Cut *) (euclidean__defs.Per C F B) as H32.
---------------------------- apply (@lemma__8__2.lemma__8__2 (B) (F) (C) H31).
---------------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C B P B) /\ (euclidean__axioms.neq F B)))) as H33.
----------------------------- exact H32.
----------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C B P B) /\ (euclidean__axioms.neq F B))))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [P H34].
assert (* AndElim *) ((euclidean__axioms.BetS C F P) /\ ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C B P B) /\ (euclidean__axioms.neq F B)))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Cong C F P F) /\ ((euclidean__axioms.Cong C B P B) /\ (euclidean__axioms.neq F B))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Cong C B P B) /\ (euclidean__axioms.neq F B)) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* Cut *) (euclidean__axioms.Cong F E C F) as H41.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H41.
----------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (E) (F) (C) H20).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F)) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
exact H45.
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E P F) as H42.
----------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (E) (C) (F) (P) (F) (H41) H37).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E F P) as H43.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E F F P) /\ ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P))) as H43.
------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (E) (P) (F) H42).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F F P) /\ ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong E F P F) /\ (euclidean__axioms.Cong F E F P)) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
exact H47.
------------------------------------ assert (* Cut *) (E = P) as H44.
------------------------------------- apply (@lemma__extensionunique.lemma__extensionunique (C) (F) (E) (P) (H19) (H35) H43).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B E B) as H45.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C F E0) -> ((euclidean__axioms.Cong F E0 F C) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong F E0 C F) -> ((euclidean__axioms.Cong F E0 P F) -> ((euclidean__axioms.Cong F E0 F P) -> (euclidean__axioms.Cong C B E0 B)))))))) with (x := E).
---------------------------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
exact H39.

--------------------------------------- exact H44.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H21.
--------------------------------------- exact H41.
--------------------------------------- exact H42.
--------------------------------------- exact H43.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B E) as H46.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B C B E) /\ ((euclidean__axioms.Cong B C E B) /\ (euclidean__axioms.Cong C B B E))) as H46.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (B) (E) (B) H45).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C B E) /\ ((euclidean__axioms.Cong B C E B) /\ (euclidean__axioms.Cong C B B E))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong B C E B) /\ (euclidean__axioms.Cong C B B E)) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
exact H47.
--------------------------------------- exact H46.
--------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H23.
---------------- exists F.
split.
----------------- exact H19.
----------------- split.
------------------ exact H11.
------------------ exact H3.
---------------- assert (* Cut *) (euclidean__defs.OS D C A B) as H24.
----------------- assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H24.
------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (C) (D) H2).
------------------ assert (* AndElim *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
exact H25.
----------------- assert (* Cut *) (euclidean__axioms.TS D A B E) as H25.
------------------ apply (@lemma__planeseparation.lemma__planeseparation (A) (B) (D) (C) (E) (H24) H23).
------------------ assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS D G E) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.nCol A B D))) as H26.
------------------- exact H25.
------------------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS D G E) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.nCol A B D)))) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [G H27].
assert (* AndElim *) ((euclidean__axioms.BetS D G E) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.nCol A B D))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.nCol A B D)) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__axioms.Cong E A C A) as H32.
----------------------- assert (* Cut *) ((euclidean__axioms.Cong E A C A) /\ (euclidean__axioms.Cong C A E A)) as H32.
------------------------ apply (@lemma__doublereverse.lemma__doublereverse (A) (C) (A) (E) H21).
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E A C A) /\ (euclidean__axioms.Cong C A E A)) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
exact H33.
----------------------- assert (* Cut *) (euclidean__axioms.Cong A E C A) as H33.
------------------------ assert (* Cut *) ((euclidean__axioms.Cong A E A C) /\ ((euclidean__axioms.Cong A E C A) /\ (euclidean__axioms.Cong E A A C))) as H33.
------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (A) (C) (A) H32).
------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A E A C) /\ ((euclidean__axioms.Cong A E C A) /\ (euclidean__axioms.Cong E A A C))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Cong A E C A) /\ (euclidean__axioms.Cong E A A C)) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
exact H36.
------------------------ assert (* Cut *) (euclidean__axioms.Cong A E D A) as H34.
------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (E) (C) (A) (D) (A) (H33) H0).
------------------------- assert (* Cut *) (euclidean__axioms.Cong A E A D) as H35.
-------------------------- assert (* Cut *) ((euclidean__axioms.Cong E A A D) /\ ((euclidean__axioms.Cong E A D A) /\ (euclidean__axioms.Cong A E A D))) as H35.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (E) (D) (A) H34).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E A A D) /\ ((euclidean__axioms.Cong E A D A) /\ (euclidean__axioms.Cong A E A D))) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Cong E A D A) /\ (euclidean__axioms.Cong A E A D)) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [H38 H39].
exact H39.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A E) as H36.
--------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (E) (D) H35).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B D B C) as H37.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong B C B D)) as H37.
----------------------------- apply (@lemma__doublereverse.lemma__doublereverse (C) (B) (D) (B) H1).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong B C B D)) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
exact H38.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong B D B E) as H38.
----------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (D) (B) (C) (B) (E) (H37) H22).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H39.
------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) G).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong G B G B) as H40.
------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) B).
------------------------------- assert (* Cut *) ((A = B) \/ ((A = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B)))))) as H41.
-------------------------------- exact H30.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D G E) as H42.
--------------------------------- assert (* Cut *) ((A = B) \/ ((A = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B)))))) as H42.
---------------------------------- exact H41.
---------------------------------- assert (* Cut *) ((A = B) \/ ((A = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B)))))) as __TmpHyp.
----------------------------------- exact H42.
----------------------------------- assert (A = B \/ (A = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B))))) as H43.
------------------------------------ exact __TmpHyp.
------------------------------------ destruct H43 as [H43|H43].
------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.Cong G D G E))) as H44.
-------------------------------------- intro H44.
apply (@H H43).
-------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.Cong G D G E)).
---------------------------------------intro H45.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H46.
---------------------------------------- exact H3.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H48.
----------------------------------------- exact H31.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H50.
------------------------------------------ exact H47.
------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H52.
------------------------------------------- exact H49.
------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H54.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H56.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H58.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H60.
----------------------------------------------- exact H57.
----------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H62.
------------------------------------------------ exact H59.
------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H64.
------------------------------------------------- exact H61.
------------------------------------------------- destruct H64 as [H64 H65].
assert (* Cut *) (False) as H66.
-------------------------------------------------- apply (@H H43).
-------------------------------------------------- assert (* Cut *) (False) as H67.
--------------------------------------------------- apply (@H44 H45).
--------------------------------------------------- assert False.
----------------------------------------------------exact H67.
---------------------------------------------------- contradiction.

------------------------------------- assert (A = G \/ (B = G) \/ ((euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B)))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44|H44].
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A E) as H45.
---------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C F A0 B F) -> ((euclidean__axioms.Col A0 B F) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (euclidean__axioms.Cong A0 D A0 E))))))))))))))))))))) with (x := A).
-----------------------------------------intro H45.
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
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
exact H62.

----------------------------------------- exact H44.
----------------------------------------- exact H.
----------------------------------------- exact H0.
----------------------------------------- exact H2.
----------------------------------------- exact H3.
----------------------------------------- exact H5.
----------------------------------------- exact H11.
----------------------------------------- exact H13.
----------------------------------------- exact H21.
----------------------------------------- exact H23.
----------------------------------------- exact H24.
----------------------------------------- exact H25.
----------------------------------------- exact H30.
----------------------------------------- exact H31.
----------------------------------------- exact H32.
----------------------------------------- exact H33.
----------------------------------------- exact H34.
----------------------------------------- exact H35.
----------------------------------------- exact H36.
----------------------------------------- exact H39.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D G E) as H46.
----------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C F A0 B F) -> ((euclidean__axioms.Col A0 B F) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> ((euclidean__axioms.Cong A0 D A0 E) -> (euclidean__axioms.Cong G D G E)))))))))))))))))))))) with (x := A).
------------------------------------------intro H46.
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
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
exact H65.

------------------------------------------ exact H44.
------------------------------------------ exact H.
------------------------------------------ exact H0.
------------------------------------------ exact H2.
------------------------------------------ exact H3.
------------------------------------------ exact H5.
------------------------------------------ exact H11.
------------------------------------------ exact H13.
------------------------------------------ exact H21.
------------------------------------------ exact H23.
------------------------------------------ exact H24.
------------------------------------------ exact H25.
------------------------------------------ exact H30.
------------------------------------------ exact H31.
------------------------------------------ exact H32.
------------------------------------------ exact H33.
------------------------------------------ exact H34.
------------------------------------------ exact H35.
------------------------------------------ exact H36.
------------------------------------------ exact H39.
------------------------------------------ exact H45.
----------------------------------------- exact H46.
--------------------------------------- assert (B = G \/ (euclidean__axioms.BetS B A G) \/ ((euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45|H45].
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D G E) as H46.
------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C F A B0 F) -> ((euclidean__axioms.Col A B0 F) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (euclidean__axioms.Cong G D G E)))))))))))))))))) with (x := B).
-------------------------------------------intro H46.
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
intro H59.
intro H60.
intro H61.
exact H60.

------------------------------------------- exact H45.
------------------------------------------- exact H.
------------------------------------------- exact H1.
------------------------------------------- exact H2.
------------------------------------------- exact H3.
------------------------------------------- exact H5.
------------------------------------------- exact H11.
------------------------------------------- exact H13.
------------------------------------------- exact H22.
------------------------------------------- exact H23.
------------------------------------------- exact H24.
------------------------------------------- exact H25.
------------------------------------------- exact H30.
------------------------------------------- exact H31.
------------------------------------------- exact H37.
------------------------------------------- exact H38.
------------------------------------------- exact H40.
------------------------------------------ exact H46.
----------------------------------------- assert (euclidean__axioms.BetS B A G \/ (euclidean__axioms.BetS A B G) \/ (euclidean__axioms.BetS A G B)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46|H46].
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H47.
-------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) A).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H48.
--------------------------------------------- exact H39.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A E) as H49.
---------------------------------------------- exact H36.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D G E G) as H50.
----------------------------------------------- apply (@euclidean__axioms.axiom__5__line (B) (A) (G) (D) (B) (A) (G) (E) (H48) (H38) (H49) (H46) (H46) H47).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D G E) as H51.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong G D G E) /\ ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E))) as H51.
------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (G) (E) (G) H50).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G D G E) /\ ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E))) as H52.
-------------------------------------------------- exact H51.
-------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E)) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
exact H52.
------------------------------------------------ exact H51.
------------------------------------------- assert (euclidean__axioms.BetS A B G \/ euclidean__axioms.BetS A G B) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47|H47].
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H48.
---------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B G B G) as H49.
----------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) G).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D G E G) as H50.
------------------------------------------------ apply (@euclidean__axioms.axiom__5__line (A) (B) (G) (D) (A) (B) (G) (E) (H49) (H36) (H38) (H47) (H47) H48).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong G D G E) as H51.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G D G E) /\ ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E))) as H51.
-------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (G) (E) (G) H50).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G D G E) /\ ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E))) as H52.
--------------------------------------------------- exact H51.
--------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Cong G D E G) /\ (euclidean__axioms.Cong D G G E)) as H54.
---------------------------------------------------- exact H53.
---------------------------------------------------- destruct H54 as [H54 H55].
exact H52.
------------------------------------------------- exact H51.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A G A G) as H48.
---------------------------------------------- exact H39.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G B G B) as H49.
----------------------------------------------- exact H40.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D G E) as H50.
------------------------------------------------ apply (@lemma__interior5.lemma__interior5 (A) (G) (B) (D) (A) (G) (B) (E) (H47) (H47) (H48) (H49) (H36) H38).
------------------------------------------------ exact H50.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A E A) as H43.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A E A) /\ ((euclidean__axioms.Cong D A A E) /\ (euclidean__axioms.Cong A D E A))) as H43.
----------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (D) (A) (E) H36).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E A) /\ ((euclidean__axioms.Cong D A A E) /\ (euclidean__axioms.Cong A D E A))) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong D A A E) /\ (euclidean__axioms.Cong A D E A)) as H46.
------------------------------------- exact H45.
------------------------------------- destruct H46 as [H46 H47].
exact H44.
---------------------------------- assert (* Cut *) (F = G) as H44.
----------------------------------- assert (* Cut *) ((A = G) \/ (euclidean__axioms.neq A G)) as H44.
------------------------------------ apply (@euclidean__tactics.eq__or__neq (A) G).
------------------------------------ assert (* Cut *) ((A = G) \/ (euclidean__axioms.neq A G)) as H45.
------------------------------------- exact H44.
------------------------------------- assert (* Cut *) ((A = G) \/ (euclidean__axioms.neq A G)) as __TmpHyp.
-------------------------------------- exact H45.
-------------------------------------- assert (A = G \/ euclidean__axioms.neq A G) as H46.
--------------------------------------- exact __TmpHyp.
--------------------------------------- destruct H46 as [H46|H46].
---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H47.
----------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H28).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E G D G) as H48.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H48.
------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (G) (D) (G) (E) H42).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
exact H49.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E B D B) as H49.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B D B) /\ (euclidean__axioms.Cong D B E B)) as H49.
-------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (D) (B) (E) H38).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B D B) /\ (euclidean__axioms.Cong D B E B)) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
exact H50.
------------------------------------------- assert (* Cut *) (~(G = B)) as H50.
-------------------------------------------- intro H50.
assert (* Cut *) (A = B) as H51.
--------------------------------------------- apply (@eq__ind euclidean__axioms.Point A (fun G0: euclidean__axioms.Point => (euclidean__axioms.BetS D G0 E) -> ((euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Cong A G0 A G0) -> ((euclidean__axioms.Cong G0 B G0 B) -> (((A = B) \/ ((A = G0) \/ ((B = G0) \/ ((euclidean__axioms.BetS B A G0) \/ ((euclidean__axioms.BetS A B G0) \/ (euclidean__axioms.BetS A G0 B)))))) -> ((euclidean__axioms.Cong G0 D G0 E) -> ((euclidean__axioms.BetS E G0 D) -> ((euclidean__axioms.Cong E G0 D G0) -> ((G0 = B) -> (A = B))))))))))) with (y := G).
----------------------------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
assert (* Cut *) (A = B) as H60.
----------------------------------------------- exact H59.
----------------------------------------------- exact H60.

---------------------------------------------- exact H46.
---------------------------------------------- exact H28.
---------------------------------------------- exact H30.
---------------------------------------------- exact H39.
---------------------------------------------- exact H40.
---------------------------------------------- exact H41.
---------------------------------------------- exact H42.
---------------------------------------------- exact H47.
---------------------------------------------- exact H48.
---------------------------------------------- exact H50.
--------------------------------------------- apply (@H H51).
-------------------------------------------- assert (* Cut *) (euclidean__defs.Per E G B) as H51.
--------------------------------------------- exists D.
split.
---------------------------------------------- exact H47.
---------------------------------------------- split.
----------------------------------------------- exact H48.
----------------------------------------------- split.
------------------------------------------------ exact H49.
------------------------------------------------ exact H50.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F C) as H52.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F C F) as H53.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C F E F) /\ (euclidean__axioms.Cong E F C F)) as H53.
------------------------------------------------ apply (@lemma__doublereverse.lemma__doublereverse (F) (E) (F) (C) H20).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C F E F) /\ (euclidean__axioms.Cong E F C F)) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
exact H55.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E B C B) as H54.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E B C B) /\ (euclidean__axioms.Cong C B E B)) as H54.
------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (C) (B) (E) H22).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B C B) /\ (euclidean__axioms.Cong C B E B)) as H55.
-------------------------------------------------- exact H54.
-------------------------------------------------- destruct H55 as [H55 H56].
exact H55.
------------------------------------------------ assert (* Cut *) (~(F = B)) as H55.
------------------------------------------------- intro H55.
assert (* Cut *) (euclidean__axioms.Cong A E A D) as H56.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B E B C) /\ ((euclidean__axioms.Cong B E C B) /\ (euclidean__axioms.Cong E B B C))) as H56.
--------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (B) (C) (B) H54).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B E B C) /\ ((euclidean__axioms.Cong B E C B) /\ (euclidean__axioms.Cong E B B C))) as H57.
---------------------------------------------------- exact H56.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong B E C B) /\ (euclidean__axioms.Cong E B B C)) as H59.
----------------------------------------------------- exact H58.
----------------------------------------------------- destruct H59 as [H59 H60].
exact H35.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H57.
--------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E A D) as H58.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__axioms.Cong E F0 C F0) -> (euclidean__axioms.BetS E A D)))))))))))) with (x := F).
-----------------------------------------------------intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C B A0 B B) -> ((euclidean__axioms.Col A0 B B) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (((A0 = B) \/ ((A0 = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A0 G) \/ ((euclidean__axioms.BetS A0 B G) \/ (euclidean__axioms.BetS A0 G B)))))) -> ((euclidean__axioms.Cong D A0 E A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.neq B A0) -> (euclidean__axioms.BetS E A0 D))))))))))))))))))))))))) with (x := A).
------------------------------------------------------intro H68.
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
exact H47.

------------------------------------------------------ exact H46.
------------------------------------------------------ exact H.
------------------------------------------------------ exact H0.
------------------------------------------------------ exact H2.
------------------------------------------------------ exact H3.
------------------------------------------------------ exact H58.
------------------------------------------------------ exact H60.
------------------------------------------------------ exact H13.
------------------------------------------------------ exact H21.
------------------------------------------------------ exact H23.
------------------------------------------------------ exact H24.
------------------------------------------------------ exact H25.
------------------------------------------------------ exact H30.
------------------------------------------------------ exact H31.
------------------------------------------------------ exact H32.
------------------------------------------------------ exact H33.
------------------------------------------------------ exact H34.
------------------------------------------------------ exact H35.
------------------------------------------------------ exact H36.
------------------------------------------------------ exact H39.
------------------------------------------------------ exact H41.
------------------------------------------------------ exact H43.
------------------------------------------------------ exact H56.
------------------------------------------------------ exact H57.

----------------------------------------------------- exact H55.
----------------------------------------------------- exact H5.
----------------------------------------------------- exact H9.
----------------------------------------------------- exact H11.
----------------------------------------------------- exact H14.
----------------------------------------------------- exact H15.
----------------------------------------------------- exact H16.
----------------------------------------------------- exact H19.
----------------------------------------------------- exact H20.
----------------------------------------------------- exact H52.
----------------------------------------------------- exact H53.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D A) as H59.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E A D A) /\ ((euclidean__axioms.Cong E A A D) /\ (euclidean__axioms.Cong A E D A))) as H59.
------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (E) (A) (D) H56).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E A D A) /\ ((euclidean__axioms.Cong E A A D) /\ (euclidean__axioms.Cong A E D A))) as H60.
------------------------------------------------------- exact H59.
------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Cong E A A D) /\ (euclidean__axioms.Cong A E D A)) as H62.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- destruct H62 as [H62 H63].
exact H60.
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E A B) as H60.
------------------------------------------------------ exists D.
split.
------------------------------------------------------- exact H58.
------------------------------------------------------- split.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H49.
--------------------------------------------------------- exact H.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per B A E) as H61.
------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (A) (B) H60).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E B C) as H62.
-------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__axioms.Cong E F0 C F0) -> (euclidean__axioms.BetS E B C)))))))))))) with (x := F).
---------------------------------------------------------intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C B A0 B B) -> ((euclidean__axioms.Col A0 B B) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (((A0 = B) \/ ((A0 = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A0 G) \/ ((euclidean__axioms.BetS A0 B G) \/ (euclidean__axioms.BetS A0 G B)))))) -> ((euclidean__axioms.Cong D A0 E A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.BetS E A0 D) -> ((euclidean__axioms.Cong E A0 D A0) -> ((euclidean__defs.Per E A0 B) -> ((euclidean__defs.Per B A0 E) -> (euclidean__axioms.BetS E B C))))))))))))))))))))))))))))) with (x := A).
----------------------------------------------------------intro H72.
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
exact H70.

---------------------------------------------------------- exact H46.
---------------------------------------------------------- exact H.
---------------------------------------------------------- exact H0.
---------------------------------------------------------- exact H2.
---------------------------------------------------------- exact H3.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- exact H13.
---------------------------------------------------------- exact H21.
---------------------------------------------------------- exact H23.
---------------------------------------------------------- exact H24.
---------------------------------------------------------- exact H25.
---------------------------------------------------------- exact H30.
---------------------------------------------------------- exact H31.
---------------------------------------------------------- exact H32.
---------------------------------------------------------- exact H33.
---------------------------------------------------------- exact H34.
---------------------------------------------------------- exact H35.
---------------------------------------------------------- exact H36.
---------------------------------------------------------- exact H39.
---------------------------------------------------------- exact H41.
---------------------------------------------------------- exact H43.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- exact H57.
---------------------------------------------------------- exact H58.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- exact H61.

--------------------------------------------------------- exact H55.
--------------------------------------------------------- exact H5.
--------------------------------------------------------- exact H9.
--------------------------------------------------------- exact H11.
--------------------------------------------------------- exact H14.
--------------------------------------------------------- exact H15.
--------------------------------------------------------- exact H16.
--------------------------------------------------------- exact H19.
--------------------------------------------------------- exact H20.
--------------------------------------------------------- exact H52.
--------------------------------------------------------- exact H53.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E B A) as H63.
--------------------------------------------------------- exists C.
split.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H54.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H32.
------------------------------------------------------------ exact H57.
--------------------------------------------------------- assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS B A J) /\ (euclidean__axioms.Cong A J A B)) as H64.
---------------------------------------------------------- apply (@lemma__extension.lemma__extension (B) (A) (A) (B) (H57) H).
---------------------------------------------------------- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS B A J) /\ (euclidean__axioms.Cong A J A B))) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [J H65].
assert (* AndElim *) ((euclidean__axioms.BetS B A J) /\ (euclidean__axioms.Cong A J A B)) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
assert (* Cut *) (euclidean__defs.Out B A J) as H68.
------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (J)).
--------------------------------------------------------------right.
right.
exact H66.

-------------------------------------------------------------- exact H57.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E B J) as H69.
-------------------------------------------------------------- apply (@lemma__8__3.lemma__8__3 (E) (B) (A) (J) (H63) H68).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J B E) as H70.
--------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (B) (J) H69).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B J) as H71.
---------------------------------------------------------------- right.
right.
right.
left.
exact H66.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A J) as H72.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A J) /\ ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))))) as H72.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (J) H71).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A J) /\ ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))))) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A)))) as H75.
-------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A)) as H79.
---------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H73.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B A E) as H73.
------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__axioms.Cong E F0 C F0) -> (euclidean__defs.Per B A E)))))))))))) with (x := F).
-------------------------------------------------------------------intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C B A0 B B) -> ((euclidean__axioms.Col A0 B B) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (((A0 = B) \/ ((A0 = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A0 G) \/ ((euclidean__axioms.BetS A0 B G) \/ (euclidean__axioms.BetS A0 G B)))))) -> ((euclidean__axioms.Cong D A0 E A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.BetS E A0 D) -> ((euclidean__axioms.Cong E A0 D A0) -> ((euclidean__defs.Per E A0 B) -> ((euclidean__defs.Per B A0 E) -> ((euclidean__defs.Per E B A0) -> ((euclidean__axioms.BetS B A0 J) -> ((euclidean__axioms.Cong A0 J A0 B) -> ((euclidean__defs.Out B A0 J) -> ((euclidean__axioms.Col A0 B J) -> ((euclidean__axioms.Col B A0 J) -> (euclidean__defs.Per B A0 E))))))))))))))))))))))))))))))))))) with (x := A).
--------------------------------------------------------------------intro H83.
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
exact H109.

-------------------------------------------------------------------- exact H46.
-------------------------------------------------------------------- exact H.
-------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------- exact H13.
-------------------------------------------------------------------- exact H21.
-------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------- exact H25.
-------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------- exact H31.
-------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------- exact H33.
-------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------- exact H39.
-------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------- exact H56.
-------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------- exact H58.
-------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------- exact H72.

------------------------------------------------------------------- exact H55.
------------------------------------------------------------------- exact H5.
------------------------------------------------------------------- exact H9.
------------------------------------------------------------------- exact H11.
------------------------------------------------------------------- exact H14.
------------------------------------------------------------------- exact H15.
------------------------------------------------------------------- exact H16.
------------------------------------------------------------------- exact H19.
------------------------------------------------------------------- exact H20.
------------------------------------------------------------------- exact H52.
------------------------------------------------------------------- exact H53.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A J) as H74.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A J) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B J))) as H74.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (J) H66).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A J) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B J))) as H75.
--------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B J)) as H77.
---------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H75.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J A) as H75.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (J) H74).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J A E) as H76.
--------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (B) (A) (J) (E) (H73) (H72) H75).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J A B) as H77.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B))))) as H77.
----------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (J) H72).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B))))) as H78.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B)))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B))) as H82.
-------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B)) as H84.
--------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
---------------------------------------------------------------------- assert (* Cut *) (A = B) as H78.
----------------------------------------------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (J) (B) (A) (E) (H76) (H70) H77).
----------------------------------------------------------------------- apply (@H H78).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E F B) as H56.
-------------------------------------------------- exists C.
split.
--------------------------------------------------- exact H52.
--------------------------------------------------- split.
---------------------------------------------------- exact H53.
---------------------------------------------------- split.
----------------------------------------------------- exact H54.
----------------------------------------------------- exact H55.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B G E) as H57.
--------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (G) (B) H51).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B F E) as H58.
---------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (F) (B) H56).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G F) as H59.
----------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (G) (F)).
------------------------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False (B) (G) (F) (H59)).
-------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (G) (F) (H41) (H11) H).


----------------------------------------------------- assert (* Cut *) (G = F) as H60.
------------------------------------------------------ apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (B) (F) (G) (E) (H57) (H58) H59).
------------------------------------------------------ assert (* Cut *) (F = G) as H61.
------------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (F) (G) H60).
------------------------------------------------------- exact H61.
---------------------------------------- assert (* Cut *) (F = G) as H47.
----------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H47.
------------------------------------------ apply (@euclidean__tactics.eq__or__neq (A) F).
------------------------------------------ assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H48.
------------------------------------------- exact H47.
------------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as __TmpHyp0.
-------------------------------------------- exact H48.
-------------------------------------------- assert (A = F \/ euclidean__axioms.neq A F) as H49.
--------------------------------------------- exact __TmpHyp0.
--------------------------------------------- destruct H49 as [H49|H49].
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H50.
----------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C F A0 B F) -> ((euclidean__axioms.Col A0 B F) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (((A0 = B) \/ ((A0 = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A0 G) \/ ((euclidean__axioms.BetS A0 B G) \/ (euclidean__axioms.BetS A0 G B)))))) -> ((euclidean__axioms.Cong D A0 E A0) -> ((euclidean__axioms.neq A0 G) -> (euclidean__axioms.neq F B)))))))))))))))))))))))) with (x := A).
------------------------------------------------intro H50.
intro H51.
intro H52.
intro H53.
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
exact H50.

------------------------------------------------ exact H49.
------------------------------------------------ exact H.
------------------------------------------------ exact H0.
------------------------------------------------ exact H2.
------------------------------------------------ exact H3.
------------------------------------------------ exact H5.
------------------------------------------------ exact H11.
------------------------------------------------ exact H13.
------------------------------------------------ exact H21.
------------------------------------------------ exact H23.
------------------------------------------------ exact H24.
------------------------------------------------ exact H25.
------------------------------------------------ exact H30.
------------------------------------------------ exact H31.
------------------------------------------------ exact H32.
------------------------------------------------ exact H33.
------------------------------------------------ exact H34.
------------------------------------------------ exact H35.
------------------------------------------------ exact H36.
------------------------------------------------ exact H39.
------------------------------------------------ exact H41.
------------------------------------------------ exact H43.
------------------------------------------------ exact H46.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F C F) as H51.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H51.
------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (E) (F) (C) H20).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F C F) /\ ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F))) as H52.
-------------------------------------------------- exact H51.
-------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Cong E F F C) /\ (euclidean__axioms.Cong F E C F)) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
exact H52.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E B C B) as H52.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B C B) /\ (euclidean__axioms.Cong C B E B)) as H52.
-------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (C) (B) (E) H22).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B C B) /\ (euclidean__axioms.Cong C B E B)) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53 H54].
exact H53.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F C) as H53.
-------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E F B) as H54.
--------------------------------------------------- exists C.
split.
---------------------------------------------------- exact H53.
---------------------------------------------------- split.
----------------------------------------------------- exact H51.
----------------------------------------------------- split.
------------------------------------------------------ exact H52.
------------------------------------------------------ exact H50.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B F E) as H55.
---------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (F) (B) H54).
---------------------------------------------------- assert (* Cut *) (~(B = G)) as H56.
----------------------------------------------------- intro H56.
assert (* Cut *) (F = A) as H57.
------------------------------------------------------ apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (F) (A) H49).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A E A C) as H58.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E A A C) /\ ((euclidean__axioms.Cong E A C A) /\ (euclidean__axioms.Cong A E A C))) as H58.
-------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (E) (C) (A) H33).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E A A C) /\ ((euclidean__axioms.Cong E A C A) /\ (euclidean__axioms.Cong A E A C))) as H59.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong E A C A) /\ (euclidean__axioms.Cong A E A C)) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
exact H62.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A D) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C A D) /\ ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D))) as H59.
--------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (D) (A) H0).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C A D) /\ ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D))) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D)) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
exact H60.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E A D) as H60.
--------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 B) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per E F0 B) -> ((euclidean__defs.Per B F0 E) -> ((F0 = A) -> (euclidean__axioms.Cong A E A D)))))))))))))))) with (y := F).
----------------------------------------------------------intro H60.
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
apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C A A B0 A) -> ((euclidean__axioms.Col A B0 A) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__defs.Per E A B0) -> ((A = A) -> (euclidean__axioms.Cong A E A D)))))))))))))))))))))))) with (x := B).
-----------------------------------------------------------intro H74.
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
exact H35.

----------------------------------------------------------- exact H56.
----------------------------------------------------------- exact H.
----------------------------------------------------------- exact H1.
----------------------------------------------------------- exact H2.
----------------------------------------------------------- exact H3.
----------------------------------------------------------- exact H60.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- exact H13.
----------------------------------------------------------- exact H22.
----------------------------------------------------------- exact H23.
----------------------------------------------------------- exact H24.
----------------------------------------------------------- exact H25.
----------------------------------------------------------- exact H30.
----------------------------------------------------------- exact H31.
----------------------------------------------------------- exact H37.
----------------------------------------------------------- exact H38.
----------------------------------------------------------- exact H40.
----------------------------------------------------------- exact H41.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- exact H52.
----------------------------------------------------------- exact H72.
----------------------------------------------------------- exact H71.
----------------------------------------------------------- exact H73.

---------------------------------------------------------- exact H49.
---------------------------------------------------------- exact H5.
---------------------------------------------------------- exact H9.
---------------------------------------------------------- exact H11.
---------------------------------------------------------- exact H14.
---------------------------------------------------------- exact H15.
---------------------------------------------------------- exact H16.
---------------------------------------------------------- exact H19.
---------------------------------------------------------- exact H20.
---------------------------------------------------------- exact H50.
---------------------------------------------------------- exact H51.
---------------------------------------------------------- exact H53.
---------------------------------------------------------- exact H54.
---------------------------------------------------------- exact H55.
---------------------------------------------------------- exact H57.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B E B D) as H61.
---------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (D) (E) H38).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H62.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H28).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E B D) as H63.
------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 B) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per E F0 B) -> ((euclidean__defs.Per B F0 E) -> ((F0 = A) -> (euclidean__axioms.BetS E B D)))))))))))))))) with (y := F).
-------------------------------------------------------------intro H63.
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
apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C A A B0 A) -> ((euclidean__axioms.Col A B0 A) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__axioms.Cong B0 E B0 D) -> ((A = A) -> (euclidean__axioms.BetS E B0 D))))))))))))))))))))))))) with (x := B).
--------------------------------------------------------------intro H77.
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
exact H62.

-------------------------------------------------------------- exact H56.
-------------------------------------------------------------- exact H.
-------------------------------------------------------------- exact H1.
-------------------------------------------------------------- exact H2.
-------------------------------------------------------------- exact H3.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- exact H13.
-------------------------------------------------------------- exact H22.
-------------------------------------------------------------- exact H23.
-------------------------------------------------------------- exact H24.
-------------------------------------------------------------- exact H25.
-------------------------------------------------------------- exact H30.
-------------------------------------------------------------- exact H31.
-------------------------------------------------------------- exact H37.
-------------------------------------------------------------- exact H38.
-------------------------------------------------------------- exact H40.
-------------------------------------------------------------- exact H41.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- exact H52.
-------------------------------------------------------------- exact H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- exact H76.

------------------------------------------------------------- exact H49.
------------------------------------------------------------- exact H5.
------------------------------------------------------------- exact H9.
------------------------------------------------------------- exact H11.
------------------------------------------------------------- exact H14.
------------------------------------------------------------- exact H15.
------------------------------------------------------------- exact H16.
------------------------------------------------------------- exact H19.
------------------------------------------------------------- exact H20.
------------------------------------------------------------- exact H50.
------------------------------------------------------------- exact H51.
------------------------------------------------------------- exact H53.
------------------------------------------------------------- exact H54.
------------------------------------------------------------- exact H55.
------------------------------------------------------------- exact H57.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E B D B) as H64.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B D B) /\ ((euclidean__axioms.Cong E B B D) /\ (euclidean__axioms.Cong B E D B))) as H64.
-------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (E) (B) (D) H61).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B D B) /\ ((euclidean__axioms.Cong E B B D) /\ (euclidean__axioms.Cong B E D B))) as H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Cong E B B D) /\ (euclidean__axioms.Cong B E D B)) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
exact H65.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D A) as H65.
-------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (D) (A) (A) H43).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H66.
--------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E B A) as H67.
---------------------------------------------------------------- exists D.
split.
----------------------------------------------------------------- exact H63.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H64.
------------------------------------------------------------------ split.
------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- exact H66.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B E) as H68.
----------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (B) (A) H67).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E A C) as H69.
------------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 B) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per E F0 B) -> ((euclidean__defs.Per B F0 E) -> ((F0 = A) -> (euclidean__axioms.BetS E A C)))))))))))))))) with (y := F).
-------------------------------------------------------------------intro H69.
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
apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C A A B0 A) -> ((euclidean__axioms.Col A B0 A) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__axioms.Cong B0 E B0 D) -> ((euclidean__axioms.BetS E B0 D) -> ((euclidean__axioms.Cong E B0 D B0) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__defs.Per E B0 A) -> ((euclidean__defs.Per A B0 E) -> ((A = A) -> (euclidean__axioms.BetS E A C)))))))))))))))))))))))))))))) with (x := B).
--------------------------------------------------------------------intro H83.
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
exact H79.

-------------------------------------------------------------------- exact H56.
-------------------------------------------------------------------- exact H.
-------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------- exact H13.
-------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------- exact H24.
-------------------------------------------------------------------- exact H25.
-------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------- exact H31.
-------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- exact H52.
-------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------- exact H82.

------------------------------------------------------------------- exact H49.
------------------------------------------------------------------- exact H5.
------------------------------------------------------------------- exact H9.
------------------------------------------------------------------- exact H11.
------------------------------------------------------------------- exact H14.
------------------------------------------------------------------- exact H15.
------------------------------------------------------------------- exact H16.
------------------------------------------------------------------- exact H19.
------------------------------------------------------------------- exact H20.
------------------------------------------------------------------- exact H50.
------------------------------------------------------------------- exact H51.
------------------------------------------------------------------- exact H53.
------------------------------------------------------------------- exact H54.
------------------------------------------------------------------- exact H55.
------------------------------------------------------------------- exact H57.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per E A B) as H70.
------------------------------------------------------------------- exists C.
split.
-------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H32.
--------------------------------------------------------------------- split.
---------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------- exact H.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B A E) as H71.
-------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 B) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per E F0 B) -> ((euclidean__defs.Per B F0 E) -> ((F0 = A) -> (euclidean__defs.Per B A E)))))))))))))))) with (y := F).
---------------------------------------------------------------------intro H71.
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
apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C A A B0 A) -> ((euclidean__axioms.Col A B0 A) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__axioms.Cong B0 E B0 D) -> ((euclidean__axioms.BetS E B0 D) -> ((euclidean__axioms.Cong E B0 D B0) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__defs.Per E B0 A) -> ((euclidean__defs.Per A B0 E) -> ((euclidean__defs.Per E A B0) -> ((A = A) -> (euclidean__defs.Per B0 A E))))))))))))))))))))))))))))))) with (x := B).
----------------------------------------------------------------------intro H85.
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
exact H104.

---------------------------------------------------------------------- exact H56.
---------------------------------------------------------------------- exact H.
---------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------- exact H73.
---------------------------------------------------------------------- exact H13.
---------------------------------------------------------------------- exact H22.
---------------------------------------------------------------------- exact H23.
---------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------- exact H25.
---------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------- exact H31.
---------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------- exact H38.
---------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------- exact H41.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------- exact H61.
---------------------------------------------------------------------- exact H63.
---------------------------------------------------------------------- exact H64.
---------------------------------------------------------------------- exact H66.
---------------------------------------------------------------------- exact H67.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------- exact H84.

--------------------------------------------------------------------- exact H49.
--------------------------------------------------------------------- exact H5.
--------------------------------------------------------------------- exact H9.
--------------------------------------------------------------------- exact H11.
--------------------------------------------------------------------- exact H14.
--------------------------------------------------------------------- exact H15.
--------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------- exact H20.
--------------------------------------------------------------------- exact H50.
--------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS A B K) /\ (euclidean__axioms.Cong B K B A)) as H72.
--------------------------------------------------------------------- apply (@lemma__extension.lemma__extension (A) (B) (B) (A) (H) H66).
--------------------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS A B K) /\ (euclidean__axioms.Cong B K B A))) as H73.
---------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------- destruct H73 as [K H73].
assert (* AndElim *) ((euclidean__axioms.BetS A B K) /\ (euclidean__axioms.Cong B K B A)) as H74.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* Cut *) (euclidean__defs.Out A B K) as H76.
------------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (A) (B) (K)).
-------------------------------------------------------------------------right.
right.
exact H74.

------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per E A K) as H77.
------------------------------------------------------------------------- apply (@lemma__8__3.lemma__8__3 (E) (A) (B) (K) (H70) H76).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per K A E) as H78.
-------------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (A) (K) H77).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A K) as H79.
--------------------------------------------------------------------------- right.
right.
right.
left.
exact H74.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B K) as H80.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B K) /\ ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))))) as H80.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (K) H79).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B K) /\ ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))))) as H81.
------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col A K B) /\ ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B)))) as H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col K B A) /\ ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B))) as H85.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col B K A) /\ (euclidean__axioms.Col K A B)) as H87.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H81.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B E) as H81.
----------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 B) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per E F0 B) -> ((euclidean__defs.Per B F0 E) -> ((F0 = A) -> (euclidean__defs.Per A B E)))))))))))))))) with (y := F).
------------------------------------------------------------------------------intro H81.
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
apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C A A B0 A) -> ((euclidean__axioms.Col A B0 A) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__axioms.Cong B0 E B0 D) -> ((euclidean__axioms.BetS E B0 D) -> ((euclidean__axioms.Cong E B0 D B0) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__defs.Per E B0 A) -> ((euclidean__defs.Per A B0 E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__axioms.BetS A B0 K) -> ((euclidean__axioms.Cong B0 K B0 A) -> ((euclidean__defs.Out A B0 K) -> ((euclidean__axioms.Col B0 A K) -> ((euclidean__axioms.Col A B0 K) -> ((A = A) -> (euclidean__defs.Per A B0 E))))))))))))))))))))))))))))))))))))) with (x := B).
-------------------------------------------------------------------------------intro H95.
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
exact H121.

------------------------------------------------------------------------------- exact H56.
------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------- exact H13.
------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------------- exact H30.
------------------------------------------------------------------------------- exact H31.
------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------- exact H40.
------------------------------------------------------------------------------- exact H41.
------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------- exact H52.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------- exact H61.
------------------------------------------------------------------------------- exact H63.
------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------- exact H94.

------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------ exact H5.
------------------------------------------------------------------------------ exact H9.
------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------ exact H14.
------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------ exact H16.
------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------ exact H57.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B K) as H82.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B K) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A K))) as H82.
------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (K) H74).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B K) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A K))) as H83.
-------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A K)) as H85.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H83.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq K B) as H83.
------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (K) H82).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per K B E) as H84.
-------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (A) (B) (K) (E) (H81) (H80) H83).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B K) as H85.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K B A) as H86.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A K) /\ ((euclidean__axioms.Col B K A) /\ ((euclidean__axioms.Col K A B) /\ ((euclidean__axioms.Col A K B) /\ (euclidean__axioms.Col K B A))))) as H86.
----------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (K) H85).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A K) /\ ((euclidean__axioms.Col B K A) /\ ((euclidean__axioms.Col K A B) /\ ((euclidean__axioms.Col A K B) /\ (euclidean__axioms.Col K B A))))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col B K A) /\ ((euclidean__axioms.Col K A B) /\ ((euclidean__axioms.Col A K B) /\ (euclidean__axioms.Col K B A)))) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col K A B) /\ ((euclidean__axioms.Col A K B) /\ (euclidean__axioms.Col K B A))) as H91.
-------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col A K B) /\ (euclidean__axioms.Col K B A)) as H93.
--------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
exact H94.
---------------------------------------------------------------------------------- assert (* Cut *) (B = A) as H87.
----------------------------------------------------------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (K) (A) (B) (E) (H84) (H78) H86).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H88.
------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong C B0 D B0) -> ((euclidean__defs.OS C D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.Perp__at C F A B0 F) -> ((euclidean__axioms.Col A B0 F) -> ((euclidean__axioms.Col A B0 H7) -> ((euclidean__axioms.Cong B0 C B0 E) -> ((euclidean__axioms.TS C A B0 E) -> ((euclidean__defs.OS D C A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.Cong B0 D B0 C) -> ((euclidean__axioms.Cong B0 D B0 E) -> ((euclidean__axioms.Cong G B0 G B0) -> (((A = B0) \/ ((A = G) \/ ((B0 = G) \/ ((euclidean__axioms.BetS B0 A G) \/ ((euclidean__axioms.BetS A B0 G) \/ (euclidean__axioms.BetS A G B0)))))) -> ((euclidean__axioms.neq F B0) -> ((euclidean__axioms.Cong E B0 C B0) -> ((euclidean__defs.Per E F B0) -> ((euclidean__defs.Per B0 F E) -> ((euclidean__axioms.Cong B0 E B0 D) -> ((euclidean__axioms.BetS E B0 D) -> ((euclidean__axioms.Cong E B0 D B0) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__defs.Per E B0 A) -> ((euclidean__defs.Per A B0 E) -> ((euclidean__defs.Per E A B0) -> ((euclidean__defs.Per B0 A E) -> ((euclidean__axioms.BetS A B0 K) -> ((euclidean__axioms.Cong B0 K B0 A) -> ((euclidean__defs.Out A B0 K) -> ((euclidean__axioms.Col B0 A K) -> ((euclidean__axioms.Col A B0 K) -> ((euclidean__defs.Per A B0 E) -> ((euclidean__axioms.neq B0 K) -> ((euclidean__axioms.neq K B0) -> ((euclidean__defs.Per K B0 E) -> ((euclidean__axioms.Col A B0 K) -> ((euclidean__axioms.Col K B0 A) -> ((B0 = A) -> (euclidean__axioms.neq B0 A))))))))))))))))))))))))))))))))))))))))))) with (x := B).
-------------------------------------------------------------------------------------intro H88.
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
apply (@eq__ind euclidean__axioms.Point A (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A G F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A G F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.neq F0 G) -> ((euclidean__axioms.Cong E F0 C F0) -> ((euclidean__axioms.BetS E F0 C) -> ((euclidean__defs.Per G F0 E) -> ((euclidean__defs.Per E F0 G) -> ((F0 = A) -> ((G = A) -> (euclidean__axioms.neq G A))))))))))))))))) with (y := F).
--------------------------------------------------------------------------------------intro H129.
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
assert (* Cut *) (A = A) as H143.
--------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------- intro H144.
exact H112.

-------------------------------------------------------------------------------------- exact H49.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- exact H9.
-------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------- exact H14.
-------------------------------------------------------------------------------------- exact H15.
-------------------------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------- exact H20.
-------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------- exact H51.
-------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------- exact H128.

------------------------------------------------------------------------------------- exact H56.
------------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------------------- exact H5.
------------------------------------------------------------------------------------- exact H11.
------------------------------------------------------------------------------------- exact H13.
------------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------------------- exact H30.
------------------------------------------------------------------------------------- exact H31.
------------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------------- exact H40.
------------------------------------------------------------------------------------- exact H41.
------------------------------------------------------------------------------------- exact H50.
------------------------------------------------------------------------------------- exact H52.
------------------------------------------------------------------------------------- exact H54.
------------------------------------------------------------------------------------- exact H55.
------------------------------------------------------------------------------------- exact H61.
------------------------------------------------------------------------------------- exact H63.
------------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------------ apply (@H66 H87).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H57.
------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (G) H56).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E G D G) as H58.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H58.
-------------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (G) (D) (G) (E) H42).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H59.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H59 as [H59 H60].
exact H59.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E B D B) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B D B) /\ (euclidean__axioms.Cong D B E B)) as H59.
--------------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (D) (B) (E) H38).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B D B) /\ (euclidean__axioms.Cong D B E B)) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
exact H60.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H60.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H28).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E G B) as H61.
---------------------------------------------------------- exists D.
split.
----------------------------------------------------------- exact H60.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H58.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H59.
------------------------------------------------------------- exact H57.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B G E) as H62.
----------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (G) (B) H61).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B G) as H63.
------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Cong C A0 D A0) -> ((euclidean__defs.OS C D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__defs.Perp__at C F A0 B F) -> ((euclidean__axioms.Col A0 B F) -> ((euclidean__axioms.Col A0 B H7) -> ((euclidean__axioms.Cong A0 C A0 E) -> ((euclidean__axioms.TS C A0 B E) -> ((euclidean__defs.OS D C A0 B) -> ((euclidean__axioms.TS D A0 B E) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.nCol A0 B D) -> ((euclidean__axioms.Cong E A0 C A0) -> ((euclidean__axioms.Cong A0 E C A0) -> ((euclidean__axioms.Cong A0 E D A0) -> ((euclidean__axioms.Cong A0 E A0 D) -> ((euclidean__axioms.Cong A0 D A0 E) -> ((euclidean__axioms.Cong A0 G A0 G) -> (((A0 = B) \/ ((A0 = G) \/ ((B = G) \/ ((euclidean__axioms.BetS B A0 G) \/ ((euclidean__axioms.BetS A0 B G) \/ (euclidean__axioms.BetS A0 G B)))))) -> ((euclidean__axioms.Cong D A0 E A0) -> ((euclidean__axioms.neq A0 G) -> (euclidean__axioms.Col F B G)))))))))))))))))))))))) with (x := A).
-------------------------------------------------------------intro H63.
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
exact H74.

------------------------------------------------------------- exact H49.
------------------------------------------------------------- exact H.
------------------------------------------------------------- exact H0.
------------------------------------------------------------- exact H2.
------------------------------------------------------------- exact H3.
------------------------------------------------------------- exact H5.
------------------------------------------------------------- exact H11.
------------------------------------------------------------- exact H13.
------------------------------------------------------------- exact H21.
------------------------------------------------------------- exact H23.
------------------------------------------------------------- exact H24.
------------------------------------------------------------- exact H25.
------------------------------------------------------------- exact H30.
------------------------------------------------------------- exact H31.
------------------------------------------------------------- exact H32.
------------------------------------------------------------- exact H33.
------------------------------------------------------------- exact H34.
------------------------------------------------------------- exact H35.
------------------------------------------------------------- exact H36.
------------------------------------------------------------- exact H39.
------------------------------------------------------------- exact H41.
------------------------------------------------------------- exact H43.
------------------------------------------------------------- exact H46.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B G F) as H64.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B F G) /\ ((euclidean__axioms.Col B G F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F G B) /\ (euclidean__axioms.Col G B F))))) as H64.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (B) (G) H63).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B F G) /\ ((euclidean__axioms.Col B G F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F G B) /\ (euclidean__axioms.Col G B F))))) as H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col B G F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F G B) /\ (euclidean__axioms.Col G B F)))) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F G B) /\ (euclidean__axioms.Col G B F))) as H69.
----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col F G B) /\ (euclidean__axioms.Col G B F)) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
exact H67.
------------------------------------------------------------- assert (* Cut *) (G = F) as H65.
-------------------------------------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (B) (F) (G) (E) (H62) (H55) H64).
-------------------------------------------------------------- assert (* Cut *) (F = G) as H66.
--------------------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (F) (G) H65).
--------------------------------------------------------------- exact H66.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F A) as H50.
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (F) H49).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F C F) as H51.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong C F E F) /\ (euclidean__axioms.Cong E F C F)) as H51.
------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (F) (E) (F) (C) H20).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C F E F) /\ (euclidean__axioms.Cong E F C F)) as H52.
-------------------------------------------------- exact H51.
-------------------------------------------------- destruct H52 as [H52 H53].
exact H53.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E F C) as H52.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E F A) as H53.
-------------------------------------------------- exists C.
split.
--------------------------------------------------- exact H52.
--------------------------------------------------- split.
---------------------------------------------------- exact H51.
---------------------------------------------------- split.
----------------------------------------------------- exact H32.
----------------------------------------------------- exact H50.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A F E) as H54.
--------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (F) (A) H53).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H55.
---------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H28).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E G D G) as H56.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H56.
------------------------------------------------------ apply (@lemma__doublereverse.lemma__doublereverse (G) (D) (G) (E) H42).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E G D G) /\ (euclidean__axioms.Cong D G E G)) as H57.
------------------------------------------------------- exact H56.
------------------------------------------------------- destruct H57 as [H57 H58].
exact H57.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D A) as H57.
------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (D) (A) (A) H43).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G A) as H58.
------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H46).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E G A) as H59.
-------------------------------------------------------- exists D.
split.
--------------------------------------------------------- exact H55.
--------------------------------------------------------- split.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H57.
----------------------------------------------------------- exact H58.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A G E) as H60.
--------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (G) (A) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A F) as H61.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H61.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H11).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H62.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H66.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H68.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- destruct H68 as [H68 H69].
exact H62.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A G) as H62.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H62.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H41).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H63.
------------------------------------------------------------- exact H62.
------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H65.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
exact H63.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H63.
------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A F G) as H64.
------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (F) (G)).
--------------------------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False (A) (F) (G) (H64)).
---------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (F) (G) (H61) (H62) H63).


------------------------------------------------------------- assert (* Cut *) (F = G) as H65.
-------------------------------------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (A) (G) (F) (E) (H54) (H60) H64).
-------------------------------------------------------------- exact H65.
----------------------------------------- exact H47.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F A F) as H45.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> (euclidean__axioms.Cong A F0 A F0)))))))))) with (x := F).
-------------------------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
exact H39.

------------------------------------- exact H44.
------------------------------------- exact H5.
------------------------------------- exact H9.
------------------------------------- exact H11.
------------------------------------- exact H14.
------------------------------------- exact H15.
------------------------------------- exact H16.
------------------------------------- exact H19.
------------------------------------- exact H20.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B F B F) as H46.
------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) F).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F A G) as H47.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> (euclidean__axioms.Cong A F0 A G)))))))))))) with (x := F).
---------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H55.

--------------------------------------- exact H44.
--------------------------------------- exact H5.
--------------------------------------- exact H9.
--------------------------------------- exact H11.
--------------------------------------- exact H14.
--------------------------------------- exact H15.
--------------------------------------- exact H16.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H45.
--------------------------------------- exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F B G) as H48.
--------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> (euclidean__axioms.Cong B F0 B G))))))))))))) with (x := F).
----------------------------------------intro H48.
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
exact H57.

---------------------------------------- exact H44.
---------------------------------------- exact H5.
---------------------------------------- exact H9.
---------------------------------------- exact H11.
---------------------------------------- exact H14.
---------------------------------------- exact H15.
---------------------------------------- exact H16.
---------------------------------------- exact H19.
---------------------------------------- exact H20.
---------------------------------------- exact H45.
---------------------------------------- exact H46.
---------------------------------------- exact H47.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H49.
---------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F B) as H50.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H50.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H11).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H57.
---------------------------------------------- exact H56.
---------------------------------------------- destruct H57 as [H57 H58].
exact H57.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B F B) as H51.
------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> ((euclidean__axioms.Cong B F0 B G) -> ((euclidean__axioms.Col A F0 B) -> (euclidean__axioms.Cong F0 B F0 B))))))))))))))) with (x := F).
-------------------------------------------intro H51.
intro H52.
intro H53.
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
exact H40.

------------------------------------------- exact H44.
------------------------------------------- exact H5.
------------------------------------------- exact H9.
------------------------------------------- exact H11.
------------------------------------------- exact H14.
------------------------------------------- exact H15.
------------------------------------------- exact H16.
------------------------------------------- exact H19.
------------------------------------------- exact H20.
------------------------------------------- exact H45.
------------------------------------------- exact H46.
------------------------------------------- exact H47.
------------------------------------------- exact H48.
------------------------------------------- exact H50.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F B G B) as H52.
------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> ((euclidean__axioms.Cong B F0 B G) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Cong F0 B F0 B) -> (euclidean__axioms.Cong F0 B G B)))))))))))))))) with (x := F).
--------------------------------------------intro H52.
intro H53.
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
exact H65.

-------------------------------------------- exact H44.
-------------------------------------------- exact H5.
-------------------------------------------- exact H9.
-------------------------------------------- exact H11.
-------------------------------------------- exact H14.
-------------------------------------------- exact H15.
-------------------------------------------- exact H16.
-------------------------------------------- exact H19.
-------------------------------------------- exact H20.
-------------------------------------------- exact H45.
-------------------------------------------- exact H46.
-------------------------------------------- exact H47.
-------------------------------------------- exact H48.
-------------------------------------------- exact H50.
-------------------------------------------- exact H51.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A D) as H53.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C A D) /\ ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D))) as H53.
--------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (D) (A) H0).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C A D) /\ ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D))) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong A C D A) /\ (euclidean__axioms.Cong C A A D)) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
exact H54.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B D) as H54.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B C B D) /\ ((euclidean__axioms.Cong B C D B) /\ (euclidean__axioms.Cong C B B D))) as H54.
---------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (B) (D) (B) H1).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C B D) /\ ((euclidean__axioms.Cong B C D B) /\ (euclidean__axioms.Cong C B B D))) as H55.
----------------------------------------------- exact H54.
----------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ (euclidean__axioms.Cong C B B D)) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
exact H55.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H55.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> ((euclidean__axioms.Cong B F0 B G) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Cong F0 B F0 B) -> ((euclidean__axioms.Cong F0 B G B) -> (euclidean__axioms.Cong A B A B))))))))))))))))) with (x := F).
-----------------------------------------------intro H55.
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
exact H49.

----------------------------------------------- exact H44.
----------------------------------------------- exact H5.
----------------------------------------------- exact H9.
----------------------------------------------- exact H11.
----------------------------------------------- exact H14.
----------------------------------------------- exact H15.
----------------------------------------------- exact H16.
----------------------------------------------- exact H19.
----------------------------------------------- exact H20.
----------------------------------------------- exact H45.
----------------------------------------------- exact H46.
----------------------------------------------- exact H47.
----------------------------------------------- exact H48.
----------------------------------------------- exact H50.
----------------------------------------------- exact H51.
----------------------------------------------- exact H52.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F C G D) as H56.
----------------------------------------------- apply (@lemma__fiveline.lemma__fiveline (A) (F) (B) (C) (A) (G) (B) (D) (H50) (H47) (H52) (H53) (H54) (H55) H).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F C F D) as H57.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> ((euclidean__axioms.Cong B F0 B G) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Cong F0 B F0 B) -> ((euclidean__axioms.Cong F0 B G B) -> ((euclidean__axioms.Cong F0 C G D) -> (euclidean__axioms.Cong F0 C F0 D)))))))))))))))))) with (x := F).
-------------------------------------------------intro H57.
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
exact H72.

------------------------------------------------- exact H44.
------------------------------------------------- exact H5.
------------------------------------------------- exact H9.
------------------------------------------------- exact H11.
------------------------------------------------- exact H14.
------------------------------------------------- exact H15.
------------------------------------------------- exact H16.
------------------------------------------------- exact H19.
------------------------------------------------- exact H20.
------------------------------------------------- exact H45.
------------------------------------------------- exact H46.
------------------------------------------------- exact H47.
------------------------------------------------- exact H48.
------------------------------------------------- exact H50.
------------------------------------------------- exact H51.
------------------------------------------------- exact H52.
------------------------------------------------- exact H56.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E F C) as H58.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H59.
-------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H28).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F D) as H60.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__defs.Perp__at C F0 A B F0) -> ((euclidean__axioms.Col C F0 F0) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.Per H7 F0 C) -> ((~(C = F0)) -> ((euclidean__axioms.neq F0 C) -> ((euclidean__axioms.BetS C F0 E) -> ((euclidean__axioms.Cong F0 E F0 C) -> ((euclidean__axioms.Cong A F0 A F0) -> ((euclidean__axioms.Cong B F0 B F0) -> ((euclidean__axioms.Cong A F0 A G) -> ((euclidean__axioms.Cong B F0 B G) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Cong F0 B F0 B) -> ((euclidean__axioms.Cong F0 B G B) -> ((euclidean__axioms.Cong F0 C G D) -> ((euclidean__axioms.Cong F0 C F0 D) -> ((euclidean__axioms.BetS E F0 C) -> (euclidean__axioms.BetS E F0 D)))))))))))))))))))) with (x := F).
----------------------------------------------------intro H60.
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
exact H59.

---------------------------------------------------- exact H44.
---------------------------------------------------- exact H5.
---------------------------------------------------- exact H9.
---------------------------------------------------- exact H11.
---------------------------------------------------- exact H14.
---------------------------------------------------- exact H15.
---------------------------------------------------- exact H16.
---------------------------------------------------- exact H19.
---------------------------------------------------- exact H20.
---------------------------------------------------- exact H45.
---------------------------------------------------- exact H46.
---------------------------------------------------- exact H47.
---------------------------------------------------- exact H48.
---------------------------------------------------- exact H50.
---------------------------------------------------- exact H51.
---------------------------------------------------- exact H52.
---------------------------------------------------- exact H56.
---------------------------------------------------- exact H57.
---------------------------------------------------- exact H58.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out F D C) as H61.
---------------------------------------------------- exists E.
split.
----------------------------------------------------- exact H58.
----------------------------------------------------- exact H60.
---------------------------------------------------- assert (* Cut *) (D = D) as H62.
----------------------------------------------------- apply (@logic.eq__refl (Point) D).
----------------------------------------------------- assert (* Cut *) (~(F = D)) as H63.
------------------------------------------------------ intro H63.
assert (* Cut *) (euclidean__axioms.Col A B F) as H64.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H64.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (B) H50).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A)))) as H67.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))) as H69.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A)) as H71.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ destruct H71 as [H71 H72].
exact H71.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B D) as H65.
-------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point F (fun X: euclidean__axioms.Point => euclidean__axioms.Col A B X)) with (y := D).
--------------------------------------------------------- exact H64.
--------------------------------------------------------- exact H63.
-------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (D) (H31) H65).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out F D D) as H64.
------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (F) (D) (D)).
--------------------------------------------------------right.
left.
exact H62.

-------------------------------------------------------- exact H63.
------------------------------------------------------- assert (* Cut *) (C = D) as H65.
-------------------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (F) (D) (C) (D) (H61) (H64) H57).
-------------------------------------------------------- exact H65.
Qed.
