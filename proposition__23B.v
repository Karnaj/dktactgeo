Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__9__5.
Require Export lemma__ABCequalsCBA.
Require Export lemma__Euclid4.
Require Export lemma__angledistinct.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__rightangleNC.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__04.
Require Export proposition__11B.
Require Export proposition__12.
Require Export proposition__23.
Definition proposition__23B : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (P: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.nCol D C E) -> ((euclidean__axioms.nCol A B P) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__defs.Out A B Y) /\ ((euclidean__defs.CongA X A Y D C E) /\ (euclidean__axioms.TS X A B P))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro P.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq B A) as H2.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
- assert (* Cut *) (exists (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__defs.Out A B G) /\ (euclidean__defs.CongA F A G D C E)) as H3.
-- apply (@proposition__23.proposition__23 (A) (B) (C) (D) (E) (H) H0).
-- assert (exists F: euclidean__axioms.Point, (exists (G: euclidean__axioms.Point), (euclidean__defs.Out A B G) /\ (euclidean__defs.CongA F A G D C E))) as H4.
--- exact H3.
--- destruct H4 as [F H4].
assert (exists G: euclidean__axioms.Point, ((euclidean__defs.Out A B G) /\ (euclidean__defs.CongA F A G D C E))) as H5.
---- exact H4.
---- destruct H5 as [G H5].
assert (* AndElim *) ((euclidean__defs.Out A B G) /\ (euclidean__defs.CongA F A G D C E)) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.neq A G) as H8.
------ apply (@lemma__raystrict.lemma__raystrict (A) (B) (G) H6).
------ assert (* Cut *) (~(euclidean__axioms.Col A B F)) as H9.
------- intro H9.
assert (* Cut *) (euclidean__defs.CongA D C E F A G) as H10.
-------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (A) (G) (D) (C) (E) H7).
-------- assert (* Cut *) (euclidean__axioms.nCol F A G) as H11.
--------- apply (@euclidean__tactics.nCol__notCol (F) (A) (G)).
----------apply (@euclidean__tactics.nCol__not__Col (F) (A) (G)).
-----------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (C) (E) (F) (A) (G) H10).


--------- assert (* Cut *) (euclidean__axioms.Col A B G) as H12.
---------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (A) (B) (G) H6).
---------- assert (* Cut *) (euclidean__axioms.Col B F G) as H13.
----------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (G)).
------------intro H13.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (G) (H13)).
-------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (F) (G) (H9) (H12) H).


----------- assert (* Cut *) (euclidean__axioms.Col B F A) as H14.
------------ assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H14.
------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H9).
------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H17.
------------ assert (* Cut *) (~(F = B)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__defs.Out A F G) as H16.
-------------- apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.CongA F0 A G D C E) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.CongA D C E F0 A G) -> ((euclidean__axioms.nCol F0 A G) -> ((euclidean__axioms.Col B F0 G) -> ((euclidean__axioms.Col B F0 A) -> (euclidean__defs.Out A F0 G)))))))) with (x := F).
---------------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
exact H6.

--------------- exact H15.
--------------- exact H7.
--------------- exact H9.
--------------- exact H10.
--------------- exact H11.
--------------- exact H13.
--------------- exact H14.
-------------- assert (* Cut *) (euclidean__axioms.Col A F G) as H17.
--------------- apply (@eq__ind__r euclidean__axioms.Point B (fun F0: euclidean__axioms.Point => (euclidean__defs.CongA F0 A G D C E) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__defs.CongA D C E F0 A G) -> ((euclidean__axioms.nCol F0 A G) -> ((euclidean__axioms.Col B F0 G) -> ((euclidean__axioms.Col B F0 A) -> ((euclidean__defs.Out A F0 G) -> (euclidean__axioms.Col A F0 G))))))))) with (x := F).
----------------intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
exact H12.

---------------- exact H15.
---------------- exact H7.
---------------- exact H9.
---------------- exact H10.
---------------- exact H11.
---------------- exact H13.
---------------- exact H14.
---------------- exact H16.
--------------- assert (* Cut *) (euclidean__axioms.Col F A G) as H18.
---------------- assert (* Cut *) ((euclidean__axioms.Col F A G) /\ ((euclidean__axioms.Col F G A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A))))) as H18.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (G) H17).
----------------- assert (* AndElim *) ((euclidean__axioms.Col F A G) /\ ((euclidean__axioms.Col F G A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A))))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col F G A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A)))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A)) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
exact H19.
---------------- apply (@euclidean__tactics.Col__nCol__False (F) (A) (G) (H11) H18).
------------- assert (* Cut *) (euclidean__axioms.neq B F) as H16.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (B) H15).
-------------- assert (* Cut *) (euclidean__axioms.Col F A G) as H17.
--------------- apply (@euclidean__tactics.not__nCol__Col (F) (A) (G)).
----------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (F) (A) (G) (H17)).
-----------------apply (@lemma__collinear4.lemma__collinear4 (B) (F) (A) (G) (H14) (H13) H16).


--------------- apply (@euclidean__tactics.Col__nCol__False (F) (A) (G) (H11) H17).
------- assert (* Cut *) (exists (H10: euclidean__axioms.Point), euclidean__defs.Perp__at F H10 A B H10) as H10.
-------- apply (@proposition__12.proposition__12 (A) (B) (F)).
---------apply (@euclidean__tactics.nCol__notCol (A) (B) (F) H9).

-------- assert (exists H11: euclidean__axioms.Point, (euclidean__defs.Perp__at F H11 A B H11)) as H12.
--------- exact H10.
--------- destruct H12 as [H11 H12].
assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.Col F H11 H11) /\ ((euclidean__axioms.Col A B H11) /\ ((euclidean__axioms.Col A B J) /\ (euclidean__defs.Per J H11 F)))) as H13.
---------- exact H12.
---------- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.Col F H11 H11) /\ ((euclidean__axioms.Col A B H11) /\ ((euclidean__axioms.Col A B J) /\ (euclidean__defs.Per J H11 F))))) as H14.
----------- exact H13.
----------- destruct H14 as [J H14].
assert (* AndElim *) ((euclidean__axioms.Col F H11 H11) /\ ((euclidean__axioms.Col A B H11) /\ ((euclidean__axioms.Col A B J) /\ (euclidean__defs.Per J H11 F)))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col A B H11) /\ ((euclidean__axioms.Col A B J) /\ (euclidean__defs.Per J H11 F))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A B J) /\ (euclidean__defs.Per J H11 F)) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* Cut *) (euclidean__axioms.nCol J H11 F) as H21.
--------------- apply (@lemma__rightangleNC.lemma__rightangleNC (J) (H11) (F) H20).
--------------- assert (* Cut *) (~(F = H11)) as H22.
---------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col A B F) as H23.
----------------- apply (@eq__ind__r euclidean__axioms.Point H11 (fun F0: euclidean__axioms.Point => (euclidean__defs.CongA F0 A G D C E) -> ((~(euclidean__axioms.Col A B F0)) -> ((euclidean__defs.Perp__at F0 H11 A B H11) -> ((euclidean__axioms.Col F0 H11 H11) -> ((euclidean__defs.Per J H11 F0) -> ((euclidean__axioms.nCol J H11 F0) -> (euclidean__axioms.Col A B F0)))))))) with (x := F).
------------------intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
exact H17.

------------------ exact H22.
------------------ exact H7.
------------------ exact H9.
------------------ exact H12.
------------------ exact H15.
------------------ exact H20.
------------------ exact H21.
----------------- apply (@H9 H23).
---------------- assert (* Cut *) (~(J = H11)) as H23.
----------------- intro H23.
assert (* Cut *) (euclidean__axioms.Col J H11 F) as H24.
------------------ left.
exact H23.
------------------ apply (@H9).
-------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
--------------------intro H25.
apply (@euclidean__tactics.Col__nCol__False (J) (H11) (F) (H21) H24).


----------------- assert (* Cut *) (euclidean__axioms.neq H11 J) as H24.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (J) (H11) H23).
------------------ assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.BetS J H11 T) /\ (euclidean__axioms.Cong H11 T H11 J)) as H25.
------------------- apply (@lemma__extension.lemma__extension (J) (H11) (H11) (J) (H23) H24).
------------------- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.BetS J H11 T) /\ (euclidean__axioms.Cong H11 T H11 J))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [T H26].
assert (* AndElim *) ((euclidean__axioms.BetS J H11 T) /\ (euclidean__axioms.Cong H11 T H11 J)) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.Col J H11 T) as H29.
---------------------- right.
right.
right.
right.
left.
exact H27.
---------------------- assert (* Cut *) (euclidean__axioms.Col B J H11) as H30.
----------------------- apply (@euclidean__tactics.not__nCol__Col (B) (J) (H11)).
------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (B) (J) (H11) (H30)).
-------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (J) (H11) (H19) (H17) H).


----------------------- assert (* Cut *) (euclidean__axioms.neq J T) as H31.
------------------------ assert (* Cut *) ((euclidean__axioms.neq H11 T) /\ ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T))) as H31.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (H11) (T) H27).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq H11 T) /\ ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T)) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
exact H35.
------------------------ assert (* Cut *) (euclidean__axioms.Col H11 J B) as H32.
------------------------- assert (* Cut *) ((euclidean__axioms.Col J B H11) /\ ((euclidean__axioms.Col J H11 B) /\ ((euclidean__axioms.Col H11 B J) /\ ((euclidean__axioms.Col B H11 J) /\ (euclidean__axioms.Col H11 J B))))) as H32.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (J) (H11) H30).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col J B H11) /\ ((euclidean__axioms.Col J H11 B) /\ ((euclidean__axioms.Col H11 B J) /\ ((euclidean__axioms.Col B H11 J) /\ (euclidean__axioms.Col H11 J B))))) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col J H11 B) /\ ((euclidean__axioms.Col H11 B J) /\ ((euclidean__axioms.Col B H11 J) /\ (euclidean__axioms.Col H11 J B)))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col H11 B J) /\ ((euclidean__axioms.Col B H11 J) /\ (euclidean__axioms.Col H11 J B))) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col B H11 J) /\ (euclidean__axioms.Col H11 J B)) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [H39 H40].
exact H40.
------------------------- assert (* Cut *) (euclidean__axioms.Col H11 J T) as H33.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col H11 J T) /\ ((euclidean__axioms.Col H11 T J) /\ ((euclidean__axioms.Col T J H11) /\ ((euclidean__axioms.Col J T H11) /\ (euclidean__axioms.Col T H11 J))))) as H33.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (J) (H11) (T) H29).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col H11 J T) /\ ((euclidean__axioms.Col H11 T J) /\ ((euclidean__axioms.Col T J H11) /\ ((euclidean__axioms.Col J T H11) /\ (euclidean__axioms.Col T H11 J))))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col H11 T J) /\ ((euclidean__axioms.Col T J H11) /\ ((euclidean__axioms.Col J T H11) /\ (euclidean__axioms.Col T H11 J)))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col T J H11) /\ ((euclidean__axioms.Col J T H11) /\ (euclidean__axioms.Col T H11 J))) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col J T H11) /\ (euclidean__axioms.Col T H11 J)) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [H40 H41].
exact H34.
-------------------------- assert (* Cut *) (euclidean__axioms.neq J H11) as H34.
--------------------------- assert (* Cut *) ((euclidean__axioms.neq H11 T) /\ ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T))) as H34.
---------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (H11) (T) H27).
---------------------------- assert (* AndElim *) ((euclidean__axioms.neq H11 T) /\ ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ (euclidean__axioms.neq J T)) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
exact H37.
--------------------------- assert (* Cut *) (euclidean__axioms.neq H11 J) as H35.
---------------------------- exact H24.
---------------------------- assert (* Cut *) (euclidean__axioms.Col J B T) as H36.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (J) (B) (T)).
------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (J) (B) (T) (H36)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (H11) (J) (B) (T) (H32) (H33) H35).


----------------------------- assert (* Cut *) (euclidean__axioms.Col J T B) as H37.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col B J T) /\ ((euclidean__axioms.Col B T J) /\ ((euclidean__axioms.Col T J B) /\ ((euclidean__axioms.Col J T B) /\ (euclidean__axioms.Col T B J))))) as H37.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (J) (B) (T) H36).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B J T) /\ ((euclidean__axioms.Col B T J) /\ ((euclidean__axioms.Col T J B) /\ ((euclidean__axioms.Col J T B) /\ (euclidean__axioms.Col T B J))))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B T J) /\ ((euclidean__axioms.Col T J B) /\ ((euclidean__axioms.Col J T B) /\ (euclidean__axioms.Col T B J)))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col T J B) /\ ((euclidean__axioms.Col J T B) /\ (euclidean__axioms.Col T B J))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col J T B) /\ (euclidean__axioms.Col T B J)) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
exact H44.
------------------------------ assert (* Cut *) (euclidean__axioms.Col B A J) as H38.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A J) /\ ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))))) as H38.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (J) H19).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A J) /\ ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A)))) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A))) as H43.
----------------------------------- exact H42.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A J B) /\ (euclidean__axioms.Col J B A)) as H45.
------------------------------------ exact H44.
------------------------------------ destruct H45 as [H45 H46].
exact H39.
------------------------------- assert (* Cut *) (euclidean__axioms.Col B A H11) as H39.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A H11) /\ ((euclidean__axioms.Col B H11 A) /\ ((euclidean__axioms.Col H11 A B) /\ ((euclidean__axioms.Col A H11 B) /\ (euclidean__axioms.Col H11 B A))))) as H39.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (H11) H17).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A H11) /\ ((euclidean__axioms.Col B H11 A) /\ ((euclidean__axioms.Col H11 A B) /\ ((euclidean__axioms.Col A H11 B) /\ (euclidean__axioms.Col H11 B A))))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B H11 A) /\ ((euclidean__axioms.Col H11 A B) /\ ((euclidean__axioms.Col A H11 B) /\ (euclidean__axioms.Col H11 B A)))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col H11 A B) /\ ((euclidean__axioms.Col A H11 B) /\ (euclidean__axioms.Col H11 B A))) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A H11 B) /\ (euclidean__axioms.Col H11 B A)) as H46.
------------------------------------- exact H45.
------------------------------------- destruct H46 as [H46 H47].
exact H40.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col A J H11) as H40.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (J) (H11)).
----------------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False (A) (J) (H11) (H40)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (J) (H11) (H38) (H39) H2).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col H11 J A) as H41.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col J A H11) /\ ((euclidean__axioms.Col J H11 A) /\ ((euclidean__axioms.Col H11 A J) /\ ((euclidean__axioms.Col A H11 J) /\ (euclidean__axioms.Col H11 J A))))) as H41.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (J) (H11) H40).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col J A H11) /\ ((euclidean__axioms.Col J H11 A) /\ ((euclidean__axioms.Col H11 A J) /\ ((euclidean__axioms.Col A H11 J) /\ (euclidean__axioms.Col H11 J A))))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col J H11 A) /\ ((euclidean__axioms.Col H11 A J) /\ ((euclidean__axioms.Col A H11 J) /\ (euclidean__axioms.Col H11 J A)))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col H11 A J) /\ ((euclidean__axioms.Col A H11 J) /\ (euclidean__axioms.Col H11 J A))) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col A H11 J) /\ (euclidean__axioms.Col H11 J A)) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
exact H49.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col J A T) as H42.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col (J) (A) (T)).
------------------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False (J) (A) (T) (H42)).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H11) (J) (A) (T) (H41) (H33) H35).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col J T A) as H43.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A J T) /\ ((euclidean__axioms.Col A T J) /\ ((euclidean__axioms.Col T J A) /\ ((euclidean__axioms.Col J T A) /\ (euclidean__axioms.Col T A J))))) as H43.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (J) (A) (T) H42).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A J T) /\ ((euclidean__axioms.Col A T J) /\ ((euclidean__axioms.Col T J A) /\ ((euclidean__axioms.Col J T A) /\ (euclidean__axioms.Col T A J))))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A T J) /\ ((euclidean__axioms.Col T J A) /\ ((euclidean__axioms.Col J T A) /\ (euclidean__axioms.Col T A J)))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col T J A) /\ ((euclidean__axioms.Col J T A) /\ (euclidean__axioms.Col T A J))) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col J T A) /\ (euclidean__axioms.Col T A J)) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
exact H50.
------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col J T P)) as H44.
------------------------------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col A B P) as H45.
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (P)).
---------------------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H45)).
----------------------------------------apply (@lemma__collinear5.lemma__collinear5 (J) (T) (A) (B) (P) (H31) (H43) (H37) H44).


-------------------------------------- apply (@H9).
---------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
----------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H1) H45).


------------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__defs.Per J H11 Q) /\ (euclidean__axioms.TS Q J T P)) as H45.
-------------------------------------- apply (@proposition__11B.proposition__11B (J) (T) (H11) (P) (H27)).
---------------------------------------apply (@euclidean__tactics.nCol__notCol (J) (T) (P) H44).

-------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__defs.Per J H11 Q) /\ (euclidean__axioms.TS Q J T P))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [Q H46].
assert (* AndElim *) ((euclidean__defs.Per J H11 Q) /\ (euclidean__axioms.TS Q J T P)) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
assert (* Cut *) (euclidean__axioms.nCol J H11 Q) as H49.
----------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (J) (H11) (Q) H47).
----------------------------------------- assert (* Cut *) (~(H11 = Q)) as H50.
------------------------------------------ intro H50.
assert (* Cut *) (euclidean__axioms.Col J H11 Q) as H51.
------------------------------------------- right.
right.
left.
exact H50.
------------------------------------------- apply (@H9).
--------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
---------------------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False (J) (H11) (Q) (H49) H51).


------------------------------------------ assert (* Cut *) (~(H11 = F)) as H51.
------------------------------------------- intro H51.
assert (* Cut *) (euclidean__axioms.Col J H11 F) as H52.
-------------------------------------------- right.
right.
left.
exact H51.
-------------------------------------------- apply (@H9).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
----------------------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False (J) (H11) (F) (H21) H52).


------------------------------------------- assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__defs.Out H11 Q S) /\ (euclidean__axioms.Cong H11 S H11 F)) as H52.
-------------------------------------------- apply (@lemma__layoff.lemma__layoff (H11) (Q) (H11) (F) (H50) H51).
-------------------------------------------- assert (exists S: euclidean__axioms.Point, ((euclidean__defs.Out H11 Q S) /\ (euclidean__axioms.Cong H11 S H11 F))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [S H53].
assert (* AndElim *) ((euclidean__defs.Out H11 Q S) /\ (euclidean__axioms.Cong H11 S H11 F)) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* Cut *) (F = F) as H56.
----------------------------------------------- apply (@logic.eq__refl (Point) F).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H57.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))))) as H57.
------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (F) (A) (G) (D) (C) (E) H7).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))))) as H58.
-------------------------------------------------- exact H57.
-------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E))))) as H60.
--------------------------------------------------- exact H59.
--------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))) as H62.
---------------------------------------------------- exact H61.
---------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E))) as H64.
----------------------------------------------------- exact H63.
----------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)) as H66.
------------------------------------------------------ exact H65.
------------------------------------------------------ destruct H66 as [H66 H67].
exact H64.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H58.
------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (C) H57).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H59.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))))) as H59.
--------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (F) (A) (G) (D) (C) (E) H7).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E))))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E))) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq D E)) as H68.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H11 A) as H60.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J H11 A) /\ ((euclidean__axioms.Col J A H11) /\ ((euclidean__axioms.Col A H11 J) /\ ((euclidean__axioms.Col H11 A J) /\ (euclidean__axioms.Col A J H11))))) as H60.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H11) (J) (A) H41).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col J H11 A) /\ ((euclidean__axioms.Col J A H11) /\ ((euclidean__axioms.Col A H11 J) /\ ((euclidean__axioms.Col H11 A J) /\ (euclidean__axioms.Col A J H11))))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col J A H11) /\ ((euclidean__axioms.Col A H11 J) /\ ((euclidean__axioms.Col H11 A J) /\ (euclidean__axioms.Col A J H11)))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A H11 J) /\ ((euclidean__axioms.Col H11 A J) /\ (euclidean__axioms.Col A J H11))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col H11 A J) /\ (euclidean__axioms.Col A J H11)) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
exact H61.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J H11 S) as H61.
---------------------------------------------------- apply (@lemma__8__3.lemma__8__3 (J) (H11) (Q) (S) (H47) H54).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Per S H11 J) as H62.
----------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (J) (H11) (S) H61).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA J H11 F J H11 S) as H63.
------------------------------------------------------ apply (@lemma__Euclid4.lemma__Euclid4 (J) (H11) (F) (J) (H11) (S) (H20) H61).
------------------------------------------------------ assert (* Cut *) (S = S) as H64.
------------------------------------------------------- apply (@logic.eq__refl (Point) S).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H11 S) as H65.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 F) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S)))))) as H65.
--------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (J) (H11) (F) (J) (H11) (S) H63).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 F) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S)))))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq H11 F) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S))))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S)))) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S))) as H72.
------------------------------------------------------------- exact H71.
------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq H11 S) /\ (euclidean__axioms.neq J S)) as H74.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- destruct H74 as [H74 H75].
exact H74.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H66.
--------------------------------------------------------- assert (* Cut *) ((A = H11) \/ (euclidean__axioms.neq A H11)) as H66.
---------------------------------------------------------- apply (@euclidean__tactics.eq__or__neq (A) H11).
---------------------------------------------------------- assert (* Cut *) ((A = H11) \/ (euclidean__axioms.neq A H11)) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- assert (* Cut *) ((A = H11) \/ (euclidean__axioms.neq A H11)) as __TmpHyp.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ assert (A = H11 \/ euclidean__axioms.neq A H11) as H68.
------------------------------------------------------------- exact __TmpHyp.
------------------------------------------------------------- destruct H68 as [H68|H68].
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J A F) as H69.
--------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H11 (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.nCol A0 B P) -> ((euclidean__axioms.neq B A0) -> ((euclidean__defs.Out A0 B G) -> ((euclidean__defs.CongA F A0 G D C E) -> ((euclidean__axioms.neq A0 G) -> ((~(euclidean__axioms.Col A0 B F)) -> ((euclidean__defs.Perp__at F H11 A0 B H11) -> ((euclidean__axioms.Col A0 B H11) -> ((euclidean__axioms.Col A0 B J) -> ((euclidean__axioms.Col B A0 J) -> ((euclidean__axioms.Col B A0 H11) -> ((euclidean__axioms.Col A0 J H11) -> ((euclidean__axioms.Col H11 J A0) -> ((euclidean__axioms.Col J A0 T) -> ((euclidean__axioms.Col J T A0) -> ((euclidean__axioms.Col J H11 A0) -> (euclidean__defs.Per J A0 F))))))))))))))))))) with (x := A).
----------------------------------------------------------------intro H69.
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
exact H20.

---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- exact H.
---------------------------------------------------------------- exact H1.
---------------------------------------------------------------- exact H2.
---------------------------------------------------------------- exact H6.
---------------------------------------------------------------- exact H7.
---------------------------------------------------------------- exact H8.
---------------------------------------------------------------- exact H9.
---------------------------------------------------------------- exact H12.
---------------------------------------------------------------- exact H17.
---------------------------------------------------------------- exact H19.
---------------------------------------------------------------- exact H38.
---------------------------------------------------------------- exact H39.
---------------------------------------------------------------- exact H40.
---------------------------------------------------------------- exact H41.
---------------------------------------------------------------- exact H42.
---------------------------------------------------------------- exact H43.
---------------------------------------------------------------- exact H60.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J A S) as H70.
---------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H11 (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.nCol A0 B P) -> ((euclidean__axioms.neq B A0) -> ((euclidean__defs.Out A0 B G) -> ((euclidean__defs.CongA F A0 G D C E) -> ((euclidean__axioms.neq A0 G) -> ((~(euclidean__axioms.Col A0 B F)) -> ((euclidean__defs.Perp__at F H11 A0 B H11) -> ((euclidean__axioms.Col A0 B H11) -> ((euclidean__axioms.Col A0 B J) -> ((euclidean__axioms.Col B A0 J) -> ((euclidean__axioms.Col B A0 H11) -> ((euclidean__axioms.Col A0 J H11) -> ((euclidean__axioms.Col H11 J A0) -> ((euclidean__axioms.Col J A0 T) -> ((euclidean__axioms.Col J T A0) -> ((euclidean__axioms.Col J H11 A0) -> ((euclidean__defs.Per J A0 F) -> (euclidean__defs.Per J A0 S)))))))))))))))))))) with (x := A).
-----------------------------------------------------------------intro H70.
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
exact H61.

----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- exact H.
----------------------------------------------------------------- exact H1.
----------------------------------------------------------------- exact H2.
----------------------------------------------------------------- exact H6.
----------------------------------------------------------------- exact H7.
----------------------------------------------------------------- exact H8.
----------------------------------------------------------------- exact H9.
----------------------------------------------------------------- exact H12.
----------------------------------------------------------------- exact H17.
----------------------------------------------------------------- exact H19.
----------------------------------------------------------------- exact H38.
----------------------------------------------------------------- exact H39.
----------------------------------------------------------------- exact H40.
----------------------------------------------------------------- exact H41.
----------------------------------------------------------------- exact H42.
----------------------------------------------------------------- exact H43.
----------------------------------------------------------------- exact H60.
----------------------------------------------------------------- exact H69.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H71.
----------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (A) (B) (G) H6).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H11 G) as H72.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (J) (H11) (G)).
-------------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (J) (H11) (G) (H72)).
--------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (A) (B) (J) (H11) (G) (H) (H19) (H17) H71).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col J A G) as H73.
------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H11 (fun A0: euclidean__axioms.Point => (euclidean__axioms.neq A0 B) -> ((euclidean__axioms.nCol A0 B P) -> ((euclidean__axioms.neq B A0) -> ((euclidean__defs.Out A0 B G) -> ((euclidean__defs.CongA F A0 G D C E) -> ((euclidean__axioms.neq A0 G) -> ((~(euclidean__axioms.Col A0 B F)) -> ((euclidean__defs.Perp__at F H11 A0 B H11) -> ((euclidean__axioms.Col A0 B H11) -> ((euclidean__axioms.Col A0 B J) -> ((euclidean__axioms.Col B A0 J) -> ((euclidean__axioms.Col B A0 H11) -> ((euclidean__axioms.Col A0 J H11) -> ((euclidean__axioms.Col H11 J A0) -> ((euclidean__axioms.Col J A0 T) -> ((euclidean__axioms.Col J T A0) -> ((euclidean__axioms.Col J H11 A0) -> ((euclidean__defs.Per J A0 F) -> ((euclidean__defs.Per J A0 S) -> ((euclidean__axioms.Col A0 B G) -> (euclidean__axioms.Col J A0 G)))))))))))))))))))))) with (x := A).
--------------------------------------------------------------------intro H73.
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
exact H72.

-------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------- exact H.
-------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------- exact H6.
-------------------------------------------------------------------- exact H7.
-------------------------------------------------------------------- exact H8.
-------------------------------------------------------------------- exact H9.
-------------------------------------------------------------------- exact H12.
-------------------------------------------------------------------- exact H17.
-------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------- exact H39.
-------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------- exact H42.
-------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------- exact H71.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H74.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H8).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per G A F) as H75.
--------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (J) (A) (G) (F) (H69) (H73) H74).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per F A G) as H76.
---------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (G) (A) (F) H75).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per G A S) as H77.
----------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (J) (A) (G) (S) (H70) (H73) H74).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per S A G) as H78.
------------------------------------------------------------------------ apply (@lemma__8__2.lemma__8__2 (G) (A) (S) H77).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H79.
------------------------------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 (F) (A) (G) (S) (A) (G) (H76) H78).
------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F H11 S H11) as H69.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F H11 S H11) /\ (euclidean__axioms.Cong S H11 F H11)) as H69.
---------------------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (H11) (S) (H11) (F) H55).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F H11 S H11) /\ (euclidean__axioms.Cong S H11 F H11)) as H70.
----------------------------------------------------------------- exact H69.
----------------------------------------------------------------- destruct H70 as [H70 H71].
exact H70.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A H11 F) as H70.
---------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (J) (H11) (A) (F) (H20) (H60) H68).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per F H11 A) as H71.
----------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (A) (H11) (F) H70).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per J H11 S) as H72.
------------------------------------------------------------------ exact H61.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per A H11 S) as H73.
------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (J) (H11) (A) (S) (H72) (H60) H68).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H11 F A H11 S) as H74.
-------------------------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 (A) (H11) (F) (A) (H11) (S) (H70) H73).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F H11 A) as H75.
--------------------------------------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (F) (H11) (A) H71).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F H11 A A H11 F) as H76.
---------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (F) (H11) (A) H75).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F H11 A A H11 S) as H77.
----------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (H11) (A) (A) (H11) (F) (A) (H11) (S) (H76) H74).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H11 S) as H78.
------------------------------------------------------------------------ apply (@lemma__rightangleNC.lemma__rightangleNC (A) (H11) (S) H73).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A H11 S S H11 A) as H79.
------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (H11) (S) H78).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F H11 A S H11 A) as H80.
-------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (H11) (A) (A) (H11) (S) (S) (H11) (A) (H77) H79).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H11 F H11 S) as H81.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H11 F H11 S) /\ ((euclidean__axioms.Cong H11 F S H11) /\ (euclidean__axioms.Cong F H11 H11 S))) as H81.
---------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (H11) (S) (H11) H69).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H11 F H11 S) /\ ((euclidean__axioms.Cong H11 F S H11) /\ (euclidean__axioms.Cong F H11 H11 S))) as H82.
----------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Cong H11 F S H11) /\ (euclidean__axioms.Cong F H11 H11 S)) as H84.
------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------ destruct H84 as [H84 H85].
exact H82.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H11 A H11 A) as H82.
---------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (H11) A).
---------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col S H11 A)) as H83.
----------------------------------------------------------------------------- intro H83.
assert (* Cut *) (euclidean__axioms.Col A H11 S) as H84.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col H11 A S) /\ ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S A H11) /\ (euclidean__axioms.Col A H11 S))))) as H84.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (S) (H11) (A) H83).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col H11 A S) /\ ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S A H11) /\ (euclidean__axioms.Col A H11 S))))) as H85.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col H11 A S) /\ ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S A H11) /\ (euclidean__axioms.Col A H11 S)))) as H87.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S A H11) /\ (euclidean__axioms.Col A H11 S))) as H89.
---------------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col S A H11) /\ (euclidean__axioms.Col A H11 S)) as H91.
----------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H92.
------------------------------------------------------------------------------ apply (@H9).
-------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
--------------------------------------------------------------------------------intro H85.
apply (@euclidean__tactics.Col__nCol__False (A) (H11) (S) (H78) H84).


----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H84.
------------------------------------------------------------------------------ apply (@proposition__04.proposition__04 (H11) (F) (A) (H11) (S) (A) (H81) (H82) H80).
------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col F A H11)) as H85.
------------------------------------------------------------------------------- intro H85.
assert (* Cut *) (euclidean__axioms.Col F H11 A) as H86.
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H86.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H88.
---------------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* Cut *) ((euclidean__axioms.Col A F H11) /\ ((euclidean__axioms.Col A H11 F) /\ ((euclidean__axioms.Col H11 F A) /\ ((euclidean__axioms.Col F H11 A) /\ (euclidean__axioms.Col H11 A F))))) as H90.
----------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (H11) H85).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A F H11) /\ ((euclidean__axioms.Col A H11 F) /\ ((euclidean__axioms.Col H11 F A) /\ ((euclidean__axioms.Col F H11 A) /\ (euclidean__axioms.Col H11 A F))))) as H91.
------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col A H11 F) /\ ((euclidean__axioms.Col H11 F A) /\ ((euclidean__axioms.Col F H11 A) /\ (euclidean__axioms.Col H11 A F)))) as H93.
------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col H11 F A) /\ ((euclidean__axioms.Col F H11 A) /\ (euclidean__axioms.Col H11 A F))) as H95.
-------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col F H11 A) /\ (euclidean__axioms.Col H11 A F)) as H97.
--------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H97.
-------------------------------------------------------------------------------- apply (@H9).
---------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
----------------------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (F) (H11) (A) (H75) H86).


------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 H11 A F) as H86.
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H86.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H88.
---------------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------------- destruct H88 as [H88 H89].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (F) (A) (H11)).
-----------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (F) (A) (H11) H85).

-------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H11 A S)) as H87.
--------------------------------------------------------------------------------- intro H87.
assert (* Cut *) (euclidean__axioms.Col S H11 A) as H88.
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H88.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H90.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ destruct H90 as [H90 H91].
assert (* Cut *) ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S H11 A) /\ ((euclidean__axioms.Col H11 S A) /\ (euclidean__axioms.Col S A H11))))) as H92.
------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H11) (A) (S) H87).
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S H11 A) /\ ((euclidean__axioms.Col H11 S A) /\ (euclidean__axioms.Col S A H11))))) as H93.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col S H11 A) /\ ((euclidean__axioms.Col H11 S A) /\ (euclidean__axioms.Col S A H11)))) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col S H11 A) /\ ((euclidean__axioms.Col H11 S A) /\ (euclidean__axioms.Col S A H11))) as H97.
---------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col H11 S A) /\ (euclidean__axioms.Col S A H11)) as H99.
----------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H97.
---------------------------------------------------------------------------------- apply (@H9).
-----------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
------------------------------------------------------------------------------------intro H89.
apply (@H83 H88).


--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H11 A S S A H11) as H88.
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H88.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H90.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ destruct H90 as [H90 H91].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H11) (A) (S)).
-------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (H11) (A) (S) H87).

---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 H11 A S) as H89.
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H89.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H91.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (H11) (H11) (A) (F) (H11) (A) (S) (H86) H92).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 S A H11) as H90.
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H90.
------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H92.
-------------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (H11) (H11) (A) (S) (S) (A) (H11) (H89) H88).
------------------------------------------------------------------------------------ assert (* Cut *) (A = A) as H91.
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H91.
-------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H93.
--------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
apply (@logic.eq__refl (Point) A).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H92.
-------------------------------------------------------------------------------------- right.
left.
exact H91.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H93.
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H93.
---------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H95.
----------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (A) (B) (G) H6).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H11 A) as H94.
---------------------------------------------------------------------------------------- assert (* Cut *) ((G = H11) \/ (euclidean__axioms.neq G H11)) as H94.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.eq__or__neq (G) H11).
----------------------------------------------------------------------------------------- assert (* Cut *) ((G = H11) \/ (euclidean__axioms.neq G H11)) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ assert (* Cut *) ((G = H11) \/ (euclidean__axioms.neq G H11)) as __TmpHyp0.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- assert (G = H11 \/ euclidean__axioms.neq G H11) as H96.
-------------------------------------------------------------------------------------------- exact __TmpHyp0.
-------------------------------------------------------------------------------------------- destruct H96 as [H96|H96].
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H11 A) as H97.
---------------------------------------------------------------------------------------------- left.
exact H96.
---------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H11 A) as H97.
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H97.
----------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H99.
------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------ destruct H99 as [H99 H100].
apply (@euclidean__tactics.not__nCol__Col (G) (H11) (A)).
-------------------------------------------------------------------------------------------------intro H101.
apply (@euclidean__tactics.Col__nCol__False (G) (H11) (A) (H101)).
--------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (A) (B) (G) (H11) (A) (H) (H93) (H17) H92).


---------------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F A) as H95.
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H95.
------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H97.
------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* Cut *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))))) as H99.
-------------------------------------------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (F) (A) (H11) (S) (A) (H11) H90).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))))) as H100.
--------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11))))) as H102.
---------------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))) as H104.
----------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11))) as H106.
------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------ destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)) as H108.
------------------------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
exact H100.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H96.
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H96.
------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H98.
-------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (A) H95).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out A F F) as H97.
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H97.
-------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H99.
--------------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
apply (@lemma__ray4.lemma__ray4 (A) (F) (F)).
----------------------------------------------------------------------------------------------right.
left.
exact H56.

---------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq S A) as H98.
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H98.
--------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H100.
---------------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* Cut *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))))) as H102.
----------------------------------------------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (F) (A) (H11) (S) (A) (H11) H90).
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))))) as H103.
------------------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11))))) as H105.
------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)))) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11))) as H109.
--------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ (euclidean__axioms.neq S H11)) as H111.
---------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H109.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A S) as H99.
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H99.
---------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H101.
----------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (S) (A) H98).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A S S) as H100.
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H100.
----------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H102.
------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------ destruct H102 as [H102 H103].
apply (@lemma__ray4.lemma__ray4 (A) (S) (S)).
-------------------------------------------------------------------------------------------------right.
left.
exact H64.

------------------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((G = H11) \/ ((G = A) \/ ((H11 = A) \/ ((euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11)))))) as H101.
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H101.
------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------ destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H103.
------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
exact H94.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H102.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((G = H11) \/ ((G = A) \/ ((H11 = A) \/ ((euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11)))))) as H102.
------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((G = H11) \/ ((G = A) \/ ((H11 = A) \/ ((euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11)))))) as __TmpHyp0.
-------------------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------------------- assert (G = H11 \/ (G = A) \/ ((H11 = A) \/ ((euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11))))) as H103.
--------------------------------------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------------------------------------- destruct H103 as [H103|H103].
---------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA F A G S A G))) as H104.
----------------------------------------------------------------------------------------------------- intro H104.
assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H105.
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H105.
------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H107.
-------------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
apply (@eq__ind__r euclidean__axioms.Point H11 (fun G0: euclidean__axioms.Point => (euclidean__defs.Out A B G0) -> ((euclidean__defs.CongA F A G0 D C E) -> ((euclidean__axioms.neq A G0) -> ((euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Col G0 H11 A) -> ((~(euclidean__defs.CongA F A G0 S A G0)) -> (euclidean__defs.CongA F A G0 S A G0)))))))) with (x := G).
---------------------------------------------------------------------------------------------------------intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
exact H90.

--------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------- exact H6.
--------------------------------------------------------------------------------------------------------- exact H7.
--------------------------------------------------------------------------------------------------------- exact H8.
--------------------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------------ apply (@H9).
-------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
--------------------------------------------------------------------------------------------------------intro H106.
apply (@H104 H105).


----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA F A G S A G)).
------------------------------------------------------------------------------------------------------intro H105.
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))))) as H106.
------------------------------------------------------------------------------------------------------- exact H0.
------------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))))) as H108.
-------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))))) as H110.
--------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))))) as H112.
---------------------------------------------------------------------------------------------------------- exact H49.
---------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))))) as H114.
----------------------------------------------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))))) as H116.
------------------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H118.
------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))))) as H120.
-------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))))) as H122.
--------------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))))) as H124.
---------------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))))) as H126.
----------------------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))))) as H128.
------------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))))) as H130.
------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H132.
-------------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))) as H134.
--------------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))) as H136.
---------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))) as H138.
----------------------------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))) as H140.
------------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))) as H142.
------------------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))) as H144.
-------------------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))) as H146.
--------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))) as H148.
---------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))) as H150.
----------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))) as H152.
------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [H152 H153].
assert (* AndElim *) ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))) as H154.
------------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))) as H156.
-------------------------------------------------------------------------------------------------------------------------------- exact H145.
-------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))) as H158.
--------------------------------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))) as H160.
---------------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))) as H162.
----------------------------------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))) as H164.
------------------------------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------------------------------ destruct H164 as [H164 H165].
assert (* AndElim *) ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))) as H166.
------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))) as H168.
-------------------------------------------------------------------------------------------------------------------------------------- exact H157.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* Cut *) (False) as H170.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@H104 H105).
--------------------------------------------------------------------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------------------------------------------------------------------exact H170.
---------------------------------------------------------------------------------------------------------------------------------------- contradiction.

---------------------------------------------------------------------------------------------------- assert (G = A \/ (H11 = A) \/ ((euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11)))) as H104.
----------------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------------- destruct H104 as [H104|H104].
------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.CongA F A G S A G))) as H105.
------------------------------------------------------------------------------------------------------- intro H105.
assert (* Cut *) (euclidean__axioms.neq A G) as H106.
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H106.
--------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H108.
---------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
apply (@eq__ind__r euclidean__axioms.Point A (fun G0: euclidean__axioms.Point => (euclidean__defs.Out A B G0) -> ((euclidean__defs.CongA F A G0 D C E) -> ((euclidean__axioms.neq A G0) -> ((euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Col G0 H11 A) -> ((~(euclidean__defs.CongA F A G0 S A G0)) -> (euclidean__axioms.neq A G0)))))))) with (x := G).
-----------------------------------------------------------------------------------------------------------intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
exact H112.

----------------------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------------------------------------- exact H7.
----------------------------------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H107.
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H107.
---------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H109.
----------------------------------------------------------------------------------------------------------- exact H108.
----------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
apply (@eq__ind__r euclidean__axioms.Point A (fun G0: euclidean__axioms.Point => (euclidean__defs.Out A B G0) -> ((euclidean__defs.CongA F A G0 D C E) -> ((euclidean__axioms.neq A G0) -> ((euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Col G0 H11 A) -> ((~(euclidean__defs.CongA F A G0 S A G0)) -> ((euclidean__axioms.neq A G0) -> (euclidean__axioms.neq G0 A))))))))) with (x := G).
------------------------------------------------------------------------------------------------------------intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
exact H117.

------------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------------ exact H6.
------------------------------------------------------------------------------------------------------------ exact H7.
------------------------------------------------------------------------------------------------------------ exact H8.
------------------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------------------ exact H106.
--------------------------------------------------------------------------------------------------------- apply (@H9).
----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
-----------------------------------------------------------------------------------------------------------intro H108.
apply (@H107 H104).


------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA F A G S A G)).
--------------------------------------------------------------------------------------------------------intro H106.
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))))) as H107.
--------------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))))) as H109.
---------------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))))) as H111.
----------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))))) as H113.
------------------------------------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))))) as H115.
------------------------------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))))) as H117.
-------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H119.
--------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))))) as H121.
---------------------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))))) as H123.
----------------------------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))))) as H125.
------------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))))) as H127.
------------------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))))) as H129.
-------------------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))))) as H131.
--------------------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H133.
---------------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))) as H135.
----------------------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))) as H137.
------------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------------ destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))) as H139.
------------------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))) as H141.
-------------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))) as H143.
--------------------------------------------------------------------------------------------------------------------------- exact H130.
--------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))) as H145.
---------------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))) as H147.
----------------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))) as H149.
------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------ destruct H149 as [H149 H150].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))) as H151.
------------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))) as H153.
-------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))) as H155.
--------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))) as H157.
---------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))) as H159.
----------------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))) as H161.
------------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------------ destruct H161 as [H161 H162].
assert (* AndElim *) ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))) as H163.
------------------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))) as H165.
-------------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))) as H167.
--------------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))) as H169.
---------------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* Cut *) (False) as H171.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@H105 H106).
----------------------------------------------------------------------------------------------------------------------------------------- assert False.
------------------------------------------------------------------------------------------------------------------------------------------exact H171.
------------------------------------------------------------------------------------------------------------------------------------------ contradiction.

------------------------------------------------------------------------------------------------------ assert (H11 = A \/ (euclidean__axioms.BetS H11 G A) \/ ((euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11))) as H105.
------------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------------- destruct H105 as [H105|H105].
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA F A G S A G))) as H106.
--------------------------------------------------------------------------------------------------------- intro H106.
assert (* Cut *) (euclidean__axioms.neq H11 A) as H107.
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H107.
----------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H109.
------------------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
apply (@eq__ind__r euclidean__axioms.Point A (fun H111: euclidean__axioms.Point => (euclidean__defs.Perp__at F H111 A B H111) -> ((euclidean__axioms.Col F H111 H111) -> ((euclidean__axioms.Col A B H111) -> ((euclidean__defs.Per J H111 F) -> ((euclidean__axioms.nCol J H111 F) -> ((~(F = H111)) -> ((~(J = H111)) -> ((euclidean__axioms.neq H111 J) -> ((euclidean__axioms.BetS J H111 T) -> ((euclidean__axioms.Cong H111 T H111 J) -> ((euclidean__axioms.Col J H111 T) -> ((euclidean__axioms.Col B J H111) -> ((euclidean__axioms.Col H111 J B) -> ((euclidean__axioms.Col H111 J T) -> ((euclidean__axioms.neq J H111) -> ((euclidean__axioms.neq H111 J) -> ((euclidean__axioms.Col B A H111) -> ((euclidean__axioms.Col A J H111) -> ((euclidean__axioms.Col H111 J A) -> ((euclidean__defs.Per J H111 Q) -> ((euclidean__axioms.nCol J H111 Q) -> ((~(H111 = Q)) -> ((~(H111 = F)) -> ((euclidean__defs.Out H111 Q S) -> ((euclidean__axioms.Cong H111 S H111 F) -> ((euclidean__axioms.Col J H111 A) -> ((euclidean__defs.Per J H111 S) -> ((euclidean__defs.Per S H111 J) -> ((euclidean__defs.CongA J H111 F J H111 S) -> ((euclidean__axioms.neq H111 S) -> ((euclidean__axioms.neq A H111) -> ((euclidean__axioms.Cong F H111 S H111) -> ((euclidean__defs.Per A H111 F) -> ((euclidean__defs.Per F H111 A) -> ((euclidean__defs.Per J H111 S) -> ((euclidean__defs.Per A H111 S) -> ((euclidean__defs.CongA A H111 F A H111 S) -> ((euclidean__axioms.nCol F H111 A) -> ((euclidean__defs.CongA F H111 A A H111 F) -> ((euclidean__defs.CongA F H111 A A H111 S) -> ((euclidean__axioms.nCol A H111 S) -> ((euclidean__defs.CongA A H111 S S H111 A) -> ((euclidean__defs.CongA F H111 A S H111 A) -> ((euclidean__axioms.Cong H111 F H111 S) -> ((euclidean__axioms.Cong H111 A H111 A) -> ((~(euclidean__axioms.Col S H111 A)) -> ((euclidean__defs.CongA H111 F A H111 S A) -> ((euclidean__defs.CongA H111 A F H111 A S) -> ((~(euclidean__axioms.Col F A H111)) -> ((euclidean__defs.CongA F A H111 H111 A F) -> ((~(euclidean__axioms.Col H111 A S)) -> ((euclidean__defs.CongA H111 A S S A H111) -> ((euclidean__defs.CongA F A H111 H111 A S) -> ((euclidean__defs.CongA F A H111 S A H111) -> ((euclidean__axioms.Col G H111 A) -> (euclidean__axioms.neq H111 A))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := H11).
-------------------------------------------------------------------------------------------------------------intro H111.
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
intro H164.
intro H165.
exact H141.

------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------- exact H12.
------------------------------------------------------------------------------------------------------------- exact H15.
------------------------------------------------------------------------------------------------------------- exact H17.
------------------------------------------------------------------------------------------------------------- exact H20.
------------------------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------------------------------------- exact H27.
------------------------------------------------------------------------------------------------------------- exact H28.
------------------------------------------------------------------------------------------------------------- exact H29.
------------------------------------------------------------------------------------------------------------- exact H30.
------------------------------------------------------------------------------------------------------------- exact H32.
------------------------------------------------------------------------------------------------------------- exact H33.
------------------------------------------------------------------------------------------------------------- exact H34.
------------------------------------------------------------------------------------------------------------- exact H35.
------------------------------------------------------------------------------------------------------------- exact H39.
------------------------------------------------------------------------------------------------------------- exact H40.
------------------------------------------------------------------------------------------------------------- exact H41.
------------------------------------------------------------------------------------------------------------- exact H47.
------------------------------------------------------------------------------------------------------------- exact H49.
------------------------------------------------------------------------------------------------------------- exact H50.
------------------------------------------------------------------------------------------------------------- exact H51.
------------------------------------------------------------------------------------------------------------- exact H54.
------------------------------------------------------------------------------------------------------------- exact H55.
------------------------------------------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------------------------------------------- exact H61.
------------------------------------------------------------------------------------------------------------- exact H62.
------------------------------------------------------------------------------------------------------------- exact H63.
------------------------------------------------------------------------------------------------------------- exact H65.
------------------------------------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------------------------------------- exact H73.
------------------------------------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------------------------------------- apply (@H9).
-----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
------------------------------------------------------------------------------------------------------------intro H108.
apply (@H107 H105).


--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA F A G S A G)).
----------------------------------------------------------------------------------------------------------intro H107.
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))))) as H108.
----------------------------------------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))))) as H110.
------------------------------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))))) as H112.
------------------------------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq J H11) /\ ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))))) as H114.
-------------------------------------------------------------------------------------------------------------- exact H49.
-------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq F H11) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))))) as H116.
--------------------------------------------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq A H11) /\ ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))))) as H118.
---------------------------------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H120.
----------------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))))) as H122.
------------------------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))))) as H124.
------------------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))))) as H126.
-------------------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq J Q) /\ ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))))) as H128.
--------------------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))))) as H130.
---------------------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.neq A S) /\ ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))))) as H132.
----------------------------------------------------------------------------------------------------------------------- exact H119.
----------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H134.
------------------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))))) as H136.
------------------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))))) as H138.
-------------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq H11 F) /\ ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))))) as H140.
--------------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq H11 Q) /\ ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))))) as H142.
---------------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq H11 A) /\ ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))))) as H144.
----------------------------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq H11 S) /\ ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))))) as H146.
------------------------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------------------------ destruct H146 as [H146 H147].
assert (* AndElim *) ((~(euclidean__axioms.BetS D C E)) /\ ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E)))) as H148.
------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B P)) /\ ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P)))) as H150.
-------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 F)) /\ ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F)))) as H152.
--------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((~(euclidean__axioms.BetS J H11 Q)) /\ ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q)))) as H154.
---------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((~(euclidean__axioms.BetS F H11 A)) /\ ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A)))) as H156.
----------------------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((~(euclidean__axioms.BetS A H11 S)) /\ ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S)))) as H158.
------------------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------------------ destruct H158 as [H158 H159].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E C)) /\ (~(euclidean__axioms.BetS C D E))) as H160.
------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((~(euclidean__axioms.BetS A P B)) /\ (~(euclidean__axioms.BetS B A P))) as H162.
-------------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((~(euclidean__axioms.BetS J F H11)) /\ (~(euclidean__axioms.BetS H11 J F))) as H164.
--------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((~(euclidean__axioms.BetS J Q H11)) /\ (~(euclidean__axioms.BetS H11 J Q))) as H166.
---------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((~(euclidean__axioms.BetS F A H11)) /\ (~(euclidean__axioms.BetS H11 F A))) as H168.
----------------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((~(euclidean__axioms.BetS A S H11)) /\ (~(euclidean__axioms.BetS H11 A S))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H170 as [H170 H171].
assert (* Cut *) (False) as H172.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@H106 H107).
------------------------------------------------------------------------------------------------------------------------------------------- assert False.
--------------------------------------------------------------------------------------------------------------------------------------------exact H172.
-------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

-------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS H11 G A \/ (euclidean__axioms.BetS G H11 A) \/ (euclidean__axioms.BetS G A H11)) as H106.
--------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------- destruct H106 as [H106|H106].
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A G H11) as H107.
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H107.
------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H109.
------------------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
apply (@euclidean__axioms.axiom__betweennesssymmetry (H11) (G) (A) H106).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A H11 G) as H108.
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H108.
------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H110.
-------------------------------------------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
apply (@lemma__ray4.lemma__ray4 (A) (H11) (G)).
---------------------------------------------------------------------------------------------------------------left.
exact H107.

--------------------------------------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F A H11 F A H11) as H109.
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H109.
-------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H111.
--------------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (F) (A) (H11)).
----------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (F) (A) (H11) H85).

------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col S A H11)) as H110.
-------------------------------------------------------------------------------------------------------------- intro H110.
assert (* Cut *) (euclidean__axioms.Col S H11 A) as H111.
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H111.
---------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H113.
----------------------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* Cut *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))))) as H115.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (S) (A) (H11) H110).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))))) as H116.
------------------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S)))) as H118.
-------------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))) as H120.
--------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S)) as H122.
---------------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
exact H122.
--------------------------------------------------------------------------------------------------------------- apply (@H9).
----------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
-----------------------------------------------------------------------------------------------------------------intro H112.
apply (@H83 H111).


-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA S A H11 S A H11) as H111.
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H111.
---------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H113.
----------------------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (S) (A) (H11)).
------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (S) (A) (H11) H110).

--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 F A G) as H112.
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H112.
----------------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H114.
------------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (A) (H11) (F) (A) (H11) (F) (G) (H109) (H97) H108).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA S A H11 S A G) as H113.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H113.
------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H115.
------------------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (S) (A) (H11) (S) (A) (H11) (S) (G) (H111) (H100) H108).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G F A H11) as H114.
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H114.
------------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H116.
-------------------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (A) (H11) (F) (A) (G) H112).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F A G S A H11) as H115.
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H115.
-------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H117.
--------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (G) (F) (A) (H11) (S) (A) (H11) (H114) H90).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H116.
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H116.
--------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H118.
---------------------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (G) (S) (A) (H11) (S) (A) (G) (H115) H113).
-------------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS G H11 A \/ euclidean__axioms.BetS G A H11) as H107.
----------------------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------------------- destruct H107 as [H107|H107].
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS A H11 G) as H108.
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H108.
-------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H110.
--------------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (H11) (A) H107).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A H11 G) as H109.
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H109.
--------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H111.
---------------------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
apply (@lemma__ray4.lemma__ray4 (A) (H11) (G)).
-----------------------------------------------------------------------------------------------------------------right.
right.
exact H108.

----------------------------------------------------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 F A H11) as H110.
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H110.
---------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H112.
----------------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (F) (A) (H11)).
------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (F) (A) (H11) H85).

--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col S A H11)) as H111.
---------------------------------------------------------------------------------------------------------------- intro H111.
assert (* Cut *) (euclidean__axioms.Col S H11 A) as H112.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H112.
------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H114.
------------------------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* Cut *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))))) as H116.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (S) (A) (H11) H111).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A S H11) /\ ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))))) as H117.
--------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col A H11 S) /\ ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S)))) as H119.
---------------------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col H11 S A) /\ ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S))) as H121.
----------------------------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col S H11 A) /\ (euclidean__axioms.Col H11 A S)) as H123.
------------------------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
exact H123.
----------------------------------------------------------------------------------------------------------------- apply (@H9).
------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
-------------------------------------------------------------------------------------------------------------------intro H113.
apply (@H83 H112).


---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA S A H11 S A H11) as H112.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H112.
------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H114.
------------------------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (S) (A) (H11)).
--------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (S) (A) (H11) H111).

----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A H11 F A G) as H113.
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H113.
------------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H115.
-------------------------------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (A) (H11) (F) (A) (H11) (F) (G) (H110) (H97) H109).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA S A H11 S A G) as H114.
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H114.
-------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H116.
--------------------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (S) (A) (H11) (S) (A) (H11) (S) (G) (H112) (H100) H109).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G F A H11) as H115.
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H115.
--------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H117.
---------------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (A) (H11) (F) (A) (G) H113).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A H11) as H116.
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H116.
---------------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H118.
----------------------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (G) (F) (A) (H11) (S) (A) (H11) (H115) H90).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H117.
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H117.
----------------------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H119.
------------------------------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (A) (G) (S) (A) (H11) (S) (A) (G) (H116) H114).
---------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS H11 A G) as H108.
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H108.
-------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H110.
--------------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (A) (H11) H107).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp H11 A F F G) as H109.
-------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp H11 A S S G) as H110.
--------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H11 A F H11 A S) as H111.
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H111.
----------------------------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H113.
------------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
exact H114.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A G S A G) as H112.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A S A) /\ ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S))) as H112.
------------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__defs.CongA H11 F A H11 S A) /\ (euclidean__defs.CongA H11 A F H11 A S)) as H114.
------------------------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
apply (@lemma__supplements.lemma__supplements (H11) (A) (F) (F) (G) (H11) (A) (S) (S) (G) (H111) (H109) H110).
----------------------------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------------ exact H102.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA S A G F A G) as H67.
---------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (A) (G) (S) (A) (G) H66).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA S A G D C E) as H68.
----------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (S) (A) (G) (F) (A) (G) (D) (C) (E) (H67) H7).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H11 S Q) as H69.
------------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 (H11) (Q) (S) H54).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col J T H11) as H70.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J H11 T) /\ ((euclidean__axioms.Col J T H11) /\ ((euclidean__axioms.Col T H11 J) /\ ((euclidean__axioms.Col H11 T J) /\ (euclidean__axioms.Col T J H11))))) as H70.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H11) (J) (T) H33).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col J H11 T) /\ ((euclidean__axioms.Col J T H11) /\ ((euclidean__axioms.Col T H11 J) /\ ((euclidean__axioms.Col H11 T J) /\ (euclidean__axioms.Col T J H11))))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col J T H11) /\ ((euclidean__axioms.Col T H11 J) /\ ((euclidean__axioms.Col H11 T J) /\ (euclidean__axioms.Col T J H11)))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col T H11 J) /\ ((euclidean__axioms.Col H11 T J) /\ (euclidean__axioms.Col T J H11))) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col H11 T J) /\ (euclidean__axioms.Col T J H11)) as H77.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ destruct H77 as [H77 H78].
exact H73.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS S J T P) as H71.
-------------------------------------------------------------- apply (@lemma__9__5.lemma__9__5 (J) (T) (P) (Q) (S) (H11) (H48) (H69) H70).
-------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS S M P) /\ ((euclidean__axioms.Col J T M) /\ (euclidean__axioms.nCol J T S))) as H72.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS S M P) /\ ((euclidean__axioms.Col J T M) /\ (euclidean__axioms.nCol J T S)))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [M H73].
assert (* AndElim *) ((euclidean__axioms.BetS S M P) /\ ((euclidean__axioms.Col J T M) /\ (euclidean__axioms.nCol J T S))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col J T M) /\ (euclidean__axioms.nCol J T S)) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* Cut *) (euclidean__axioms.Col T A B) as H78.
------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (T) (A) (B)).
--------------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (T) (A) (B) (H78)).
---------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (J) (T) (A) (B) (H43) (H37) H31).


------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B T) as H79.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T B A) /\ (euclidean__axioms.Col B A T))))) as H79.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (T) (A) (B) H78).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A T B) /\ ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T B A) /\ (euclidean__axioms.Col B A T))))) as H80.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A B T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T B A) /\ (euclidean__axioms.Col B A T)))) as H82.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T B A) /\ (euclidean__axioms.Col B A T))) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col T B A) /\ (euclidean__axioms.Col B A T)) as H86.
------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H82.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A T) as H80.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A))))) as H80.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (T) H79).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A))))) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A)))) as H83.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A))) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A)) as H87.
-------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H81.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A J T) as H81.
---------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (J) (T)).
-----------------------------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False (A) (J) (T) (H81)).
------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (J) (T) (H38) (H80) H2).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J T A) as H82.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J A T) /\ ((euclidean__axioms.Col J T A) /\ ((euclidean__axioms.Col T A J) /\ ((euclidean__axioms.Col A T J) /\ (euclidean__axioms.Col T J A))))) as H82.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (J) (T) H81).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col J A T) /\ ((euclidean__axioms.Col J T A) /\ ((euclidean__axioms.Col T A J) /\ ((euclidean__axioms.Col A T J) /\ (euclidean__axioms.Col T J A))))) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col J T A) /\ ((euclidean__axioms.Col T A J) /\ ((euclidean__axioms.Col A T J) /\ (euclidean__axioms.Col T J A)))) as H85.
-------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col T A J) /\ ((euclidean__axioms.Col A T J) /\ (euclidean__axioms.Col T J A))) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col A T J) /\ (euclidean__axioms.Col T J A)) as H89.
---------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H85.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B J T) as H83.
------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (J) (T)).
-------------------------------------------------------------------------intro H83.
apply (@euclidean__tactics.Col__nCol__False (B) (J) (T) (H83)).
--------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (J) (T) (H19) (H79) H).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col J T B) as H84.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J B T) /\ ((euclidean__axioms.Col J T B) /\ ((euclidean__axioms.Col T B J) /\ ((euclidean__axioms.Col B T J) /\ (euclidean__axioms.Col T J B))))) as H84.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (J) (T) H83).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col J B T) /\ ((euclidean__axioms.Col J T B) /\ ((euclidean__axioms.Col T B J) /\ ((euclidean__axioms.Col B T J) /\ (euclidean__axioms.Col T J B))))) as H85.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col J T B) /\ ((euclidean__axioms.Col T B J) /\ ((euclidean__axioms.Col B T J) /\ (euclidean__axioms.Col T J B)))) as H87.
---------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col T B J) /\ ((euclidean__axioms.Col B T J) /\ (euclidean__axioms.Col T J B))) as H89.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col B T J) /\ (euclidean__axioms.Col T J B)) as H91.
------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------ destruct H91 as [H91 H92].
exact H87.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H85.
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (M)).
---------------------------------------------------------------------------intro H85.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (M) (H85)).
----------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (J) (T) (A) (B) (M) (H31) (H82) (H84) H76).


-------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B S)) as H86.
--------------------------------------------------------------------------- intro H86.
assert (* Cut *) (euclidean__axioms.Col J T S) as H87.
---------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (J) (T) (S)).
-----------------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (J) (T) (S) (H87)).
------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (A) (B) (J) (T) (S) (H) (H19) (H79) H86).


---------------------------------------------------------------------------- apply (@H9).
-----------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
------------------------------------------------------------------------------intro H88.
apply (@euclidean__tactics.Col__nCol__False (J) (T) (S) (H77) H87).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS S A B P) as H87.
---------------------------------------------------------------------------- exists M.
split.
----------------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (A) (B) (S) H86).
---------------------------------------------------------------------------- exists S.
exists G.
split.
----------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------ exact H87.
Qed.
