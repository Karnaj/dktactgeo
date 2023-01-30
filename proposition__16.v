Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Require Export proposition__04.
Require Export proposition__10.
Require Export proposition__15.
Definition proposition__16 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.BetS B C D) -> ((euclidean__defs.LtA B A C A C D) /\ (euclidean__defs.LtA C B A A C D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H1.
- exact H.
- assert (* Cut *) (~(A = C)) as H2.
-- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
--- right.
left.
exact H2.
--- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H3).
-- assert (* Cut *) (~(B = C)) as H3.
--- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
---- right.
right.
left.
exact H3.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H4).
--- assert (* Cut *) (euclidean__axioms.neq C B) as H4.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H3).
---- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E C) /\ (euclidean__axioms.Cong E A E C)) as H5.
----- apply (@proposition__10.proposition__10 (A) (C) H2).
----- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A E C) /\ (euclidean__axioms.Cong E A E C))) as H6.
------ exact H5.
------ destruct H6 as [E H6].
assert (* AndElim *) ((euclidean__axioms.BetS A E C) /\ (euclidean__axioms.Cong E A E C)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* Cut *) (~(B = E)) as H9.
-------- intro H9.
assert (* Cut *) (euclidean__axioms.BetS A B C) as H10.
--------- apply (@eq__ind__r euclidean__axioms.Point E (fun B0: euclidean__axioms.Point => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__axioms.BetS B0 C D) -> ((euclidean__axioms.nCol A B0 C) -> ((~(B0 = C)) -> ((euclidean__axioms.neq C B0) -> (euclidean__axioms.BetS A B0 C))))))) with (x := B).
----------intro H10.
intro H11.
intro H12.
intro H13.
intro H14.
exact H7.

---------- exact H9.
---------- exact H.
---------- exact H0.
---------- exact H1.
---------- exact H3.
---------- exact H4.
--------- assert (* Cut *) (euclidean__axioms.Col A B C) as H11.
---------- right.
right.
right.
right.
left.
exact H10.
---------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H11).
-------- assert (* Cut *) (euclidean__axioms.neq E B) as H10.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H9).
--------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B E F) /\ (euclidean__axioms.Cong E F E B)) as H11.
---------- apply (@lemma__extension.lemma__extension (B) (E) (E) (B) (H9) H10).
---------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B E F) /\ (euclidean__axioms.Cong E F E B))) as H12.
----------- exact H11.
----------- destruct H12 as [F H12].
assert (* AndElim *) ((euclidean__axioms.BetS B E F) /\ (euclidean__axioms.Cong E F E B)) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* Cut *) (~(A = C)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.Col A B C) as H16.
-------------- right.
left.
exact H15.
-------------- apply (@H2 H15).
------------- assert (* Cut *) (euclidean__axioms.neq C A) as H16.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H15).
-------------- assert (* Cut *) (euclidean__axioms.neq E C) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H17.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (C) H7).
---------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
exact H18.
--------------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS A C G) /\ (euclidean__axioms.Cong C G E C)) as H18.
---------------- apply (@lemma__extension.lemma__extension (A) (C) (E) (C) (H15) H17).
---------------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS A C G) /\ (euclidean__axioms.Cong C G E C))) as H19.
----------------- exact H18.
----------------- destruct H19 as [G H19].
assert (* AndElim *) ((euclidean__axioms.BetS A C G) /\ (euclidean__axioms.Cong C G E C)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* Cut *) (~(euclidean__axioms.Col B E A)) as H22.
------------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col A E C) as H23.
-------------------- right.
right.
right.
right.
left.
exact H7.
-------------------- assert (* Cut *) (euclidean__axioms.Col E A B) as H24.
--------------------- assert (* Cut *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))))) as H24.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (A) H22).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))))) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B)))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B)) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
exact H27.
--------------------- assert (* Cut *) (euclidean__axioms.Col E A C) as H25.
---------------------- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H25.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H23).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
exact H26.
---------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H26.
----------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H26.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (C) H7).
------------------------ assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
exact H29.
----------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H27.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (E) H26).
------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H28.
------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
--------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H28)).
---------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (B) (C) (H24) (H25) H27).


------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H28).
------------------- assert (* Cut *) (euclidean__defs.CongA B E A C E F) as H23.
-------------------- apply (@proposition__15.proposition__15a (B) (F) (A) (C) (E) (H13) (H7)).
---------------------apply (@euclidean__tactics.nCol__notCol (B) (E) (A) H22).

-------------------- assert (* Cut *) (~(euclidean__axioms.Col A E B)) as H24.
--------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col B E A) as H25.
---------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H25.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H24).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
exact H33.
---------------------- apply (@H22 H25).
--------------------- assert (* Cut *) (euclidean__defs.CongA A E B B E A) as H25.
---------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (E) (B)).
-----------------------apply (@euclidean__tactics.nCol__notCol (A) (E) (B) H24).

---------------------- assert (* Cut *) (euclidean__defs.CongA A E B C E F) as H26.
----------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (E) (B) (B) (E) (A) (C) (E) (F) (H25) H23).
----------------------- assert (* Cut *) (euclidean__axioms.Cong B E F E) as H27.
------------------------ assert (* Cut *) ((euclidean__axioms.Cong B E F E) /\ (euclidean__axioms.Cong F E B E)) as H27.
------------------------- apply (@lemma__doublereverse.lemma__doublereverse (E) (F) (E) (B) H14).
------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B E F E) /\ (euclidean__axioms.Cong F E B E)) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
exact H28.
------------------------ assert (* Cut *) (euclidean__axioms.Cong E B E F) as H28.
------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B E F) /\ ((euclidean__axioms.Cong E B F E) /\ (euclidean__axioms.Cong B E E F))) as H28.
-------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (E) (F) (E) H27).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B E F) /\ ((euclidean__axioms.Cong E B F E) /\ (euclidean__axioms.Cong B E E F))) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Cong E B F E) /\ (euclidean__axioms.Cong B E E F)) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
exact H29.
------------------------- assert (* Cut *) (~(euclidean__axioms.Col E A B)) as H29.
-------------------------- intro H29.
assert (* Cut *) (euclidean__axioms.Col B E A) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))))) as H30.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (B) H29).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H35.
--------------------------- apply (@H22 H30).
-------------------------- assert (* Cut *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H30.
--------------------------- apply (@proposition__04.proposition__04 (E) (A) (B) (E) (C) (F) (H8) (H28) H26).
--------------------------- assert (* Cut *) (~(euclidean__axioms.Col B A E)) as H31.
---------------------------- intro H31.
assert (* Cut *) (euclidean__axioms.Col E A B) as H32.
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H32.
------------------------------ exact H30.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H36.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (E) H31).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
exact H44.
----------------------------- apply (@H22).
------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------intro H33.
apply (@H29 H32).


---------------------------- assert (* Cut *) (euclidean__defs.Out A C E) as H32.
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H32.
------------------------------ exact H30.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
apply (@lemma__ray4.lemma__ray4 (A) (C) (E)).
--------------------------------left.
exact H7.

-------------------------------- exact H15.
----------------------------- assert (* Cut *) (B = B) as H33.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H33.
------------------------------- exact H30.
------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
apply (@logic.eq__refl (Point) B).
------------------------------ assert (* Cut *) (euclidean__axioms.neq A B) as H34.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H34.
-------------------------------- exact H30.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
assert (* Cut *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F)))))) as H38.
---------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (E) (A) (B) (E) (C) (F) H36).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F)))))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F))))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F)))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq E F)) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
exact H41.
------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H35.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H35.
--------------------------------- exact H30.
--------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H34).
-------------------------------- assert (* Cut *) (euclidean__defs.Out A B B) as H36.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H36.
---------------------------------- exact H30.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
apply (@lemma__ray4.lemma__ray4 (A) (B) (B)).
------------------------------------right.
left.
exact H33.

------------------------------------ exact H34.
--------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H37.
---------------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.Col A B C) as H38.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H38.
------------------------------------ exact H30.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H42.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H37).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
exact H43.
----------------------------------- apply (@H22).
------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------------intro H39.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H38).


---------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C B A C) as H38.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H38.
------------------------------------ exact H30.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (B) (A) (C)).
--------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (A) (C) H37).

----------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C B A E) as H39.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H39.
------------------------------------- exact H30.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (B) (A) (C) (B) (A) (C) (B) (E) (H38) (H36) H32).
------------------------------------ assert (* Cut *) (euclidean__defs.CongA B A E E A B) as H40.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H40.
-------------------------------------- exact H30.
-------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [H42 H43].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (A) (E)).
----------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (A) (E) H31).

------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C E A B) as H41.
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H41.
--------------------------------------- exact H30.
--------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (A) (C) (B) (A) (E) (E) (A) (B) (H39) H40).
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C E C F) as H42.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H42.
---------------------------------------- exact H30.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (A) (C) (E) (A) (B) (E) (C) (F) (H41) H44).
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C E A) as H43.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H43.
----------------------------------------- exact H30.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (C) H7).
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H44.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H44.
------------------------------------------ exact H30.
------------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H46.
------------------------------------------- exact H45.
------------------------------------------- destruct H46 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A))) as H48.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (A) H43).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A))) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A)) as H51.
---------------------------------------------- exact H50.
---------------------------------------------- destruct H51 as [H51 H52].
exact H51.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out C E A) as H45.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H45.
------------------------------------------- exact H30.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
apply (@lemma__ray4.lemma__ray4 (C) (E) (A)).
---------------------------------------------right.
right.
exact H43.

--------------------------------------------- exact H44.
------------------------------------------ assert (* Cut *) (F = F) as H46.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H46.
-------------------------------------------- exact H30.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
apply (@logic.eq__refl (Point) F).
------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E C F)) as H47.
-------------------------------------------- intro H47.
assert (* Cut *) (euclidean__axioms.Col B E F) as H48.
--------------------------------------------- right.
right.
right.
right.
left.
exact H13.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E B) as H49.
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H49.
----------------------------------------------- exact H30.
----------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H51.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H51 as [H51 H52].
assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H53.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (F) H48).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)))) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))) as H58.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
exact H61.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E C) as H50.
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H50.
------------------------------------------------ exact H30.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52 H53].
assert (* Cut *) ((euclidean__axioms.Col C E F) /\ ((euclidean__axioms.Col C F E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E F C) /\ (euclidean__axioms.Col F C E))))) as H54.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (F) H47).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C E F) /\ ((euclidean__axioms.Col C F E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E F C) /\ (euclidean__axioms.Col F C E))))) as H55.
--------------------------------------------------- exact H54.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col C F E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E F C) /\ (euclidean__axioms.Col F C E)))) as H57.
---------------------------------------------------- exact H56.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E F C) /\ (euclidean__axioms.Col F C E))) as H59.
----------------------------------------------------- exact H58.
----------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col E F C) /\ (euclidean__axioms.Col F C E)) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
exact H59.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H51.
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H51.
------------------------------------------------- exact H30.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H53.
-------------------------------------------------- exact H52.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F))) as H55.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (F) H13).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F))) as H56.
---------------------------------------------------- exact H55.
---------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F)) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
exact H56.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F E) as H52.
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H52.
-------------------------------------------------- exact H30.
-------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H51).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B C) as H53.
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H53.
--------------------------------------------------- exact H30.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
apply (@euclidean__tactics.not__nCol__Col (E) (B) (C)).
-----------------------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False (E) (B) (C) (H57)).
------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (E) (B) (C) (H49) (H50) H52).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H54.
--------------------------------------------------- right.
right.
right.
right.
left.
exact H7.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C B) as H55.
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H55.
----------------------------------------------------- exact H30.
----------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H57.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H57 as [H57 H58].
assert (* Cut *) ((euclidean__axioms.Col B E C) /\ ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E C B) /\ (euclidean__axioms.Col C B E))))) as H59.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (B) (C) H53).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E C B) /\ (euclidean__axioms.Col C B E))))) as H60.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E C B) /\ (euclidean__axioms.Col C B E)))) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E C B) /\ (euclidean__axioms.Col C B E))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ (euclidean__axioms.Col C B E)) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
exact H66.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C A) as H56.
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H56.
------------------------------------------------------ exact H30.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H60.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H54).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H67.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ destruct H67 as [H67 H68].
exact H63.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H57.
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H57.
------------------------------------------------------- exact H30.
------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [H59 H60].
assert (* Cut *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A))) as H61.
--------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (A) H43).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A))) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C A)) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
exact H17.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B A) as H58.
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H58.
-------------------------------------------------------- exact H30.
-------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [H60 H61].
apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
----------------------------------------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (A) (H62)).
-----------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (C) (B) (A) (H55) (H56) H57).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H59.
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H59.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H63.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H58).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
exact H71.
-------------------------------------------------------- apply (@H22).
---------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
----------------------------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H59).


-------------------------------------------- assert (* Cut *) (~(C = F)) as H48.
--------------------------------------------- intro H48.
assert (* Cut *) (euclidean__axioms.Col E C F) as H49.
---------------------------------------------- right.
right.
left.
exact H48.
---------------------------------------------- apply (@H22).
-----------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
------------------------------------------------intro H50.
apply (@H47 H49).


--------------------------------------------- assert (* Cut *) (euclidean__defs.Out C F F) as H49.
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H49.
----------------------------------------------- exact H30.
----------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H51.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H51 as [H51 H52].
apply (@lemma__ray4.lemma__ray4 (C) (F) (F)).
-------------------------------------------------right.
left.
exact H46.

------------------------------------------------- exact H48.
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E C F E C F) as H50.
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H50.
------------------------------------------------ exact H30.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52 H53].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (E) (C) (F)).
--------------------------------------------------apply (@euclidean__tactics.nCol__notCol (E) (C) (F) H47).

----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E C F A C F) as H51.
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H51.
------------------------------------------------- exact H30.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H53.
-------------------------------------------------- exact H52.
-------------------------------------------------- destruct H53 as [H53 H54].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (E) (C) (F) (E) (C) (F) (A) (F) (H50) (H45) H49).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B A C A C F) as H52.
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H52.
-------------------------------------------------- exact H30.
-------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (A) (C) (E) (C) (F) (A) (C) (F) (H42) H51).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D C B) as H53.
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H53.
--------------------------------------------------- exact H30.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (D) H0).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E B) as H54.
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H54.
---------------------------------------------------- exact H30.
---------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H56.
----------------------------------------------------- exact H55.
----------------------------------------------------- destruct H56 as [H56 H57].
apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (E) (F) H13).
--------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D B F)) as H55.
---------------------------------------------------- intro H55.
assert (* Cut *) (euclidean__axioms.Col F B D) as H56.
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H56.
------------------------------------------------------ exact H30.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
assert (* Cut *) ((euclidean__axioms.Col B D F) /\ ((euclidean__axioms.Col B F D) /\ ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D F B) /\ (euclidean__axioms.Col F B D))))) as H60.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (F) H55).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B D F) /\ ((euclidean__axioms.Col B F D) /\ ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D F B) /\ (euclidean__axioms.Col F B D))))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B F D) /\ ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D F B) /\ (euclidean__axioms.Col F B D)))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D F B) /\ (euclidean__axioms.Col F B D))) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col D F B) /\ (euclidean__axioms.Col F B D)) as H67.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ destruct H67 as [H67 H68].
exact H68.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E F) as H57.
------------------------------------------------------ right.
right.
right.
right.
left.
exact H13.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F B E) as H58.
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H58.
-------------------------------------------------------- exact H30.
-------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [H60 H61].
assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H62.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (F) H57).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B)) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H59.
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H59.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F))) as H63.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (F) H13).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F)) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
exact H67.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H60.
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H60.
---------------------------------------------------------- exact H30.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (F) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B D E) as H61.
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H61.
----------------------------------------------------------- exact H30.
----------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H63.
------------------------------------------------------------ exact H62.
------------------------------------------------------------ destruct H63 as [H63 H64].
apply (@euclidean__tactics.not__nCol__Col (B) (D) (E)).
-------------------------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False (B) (D) (E) (H65)).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (B) (D) (E) (H56) (H58) H60).


---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B E) as H62.
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H62.
------------------------------------------------------------ exact H30.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* Cut *) ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B E D) /\ (euclidean__axioms.Col E D B))))) as H66.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (D) (E) H61).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B E D) /\ (euclidean__axioms.Col E D B))))) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B E D) /\ (euclidean__axioms.Col E D B)))) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B E D) /\ (euclidean__axioms.Col E D B))) as H71.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B E D) /\ (euclidean__axioms.Col E D B)) as H73.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H73 as [H73 H74].
exact H67.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H63.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H0.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H64.
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H64.
-------------------------------------------------------------- exact H30.
-------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H66.
--------------------------------------------------------------- exact H65.
--------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H68.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H63).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H69.
----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H75.
-------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H73.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H65.
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H65.
--------------------------------------------------------------- exact H30.
--------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H69.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (C) (D) H0).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H70.
------------------------------------------------------------------ exact H69.
------------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)) as H72.
------------------------------------------------------------------- exact H71.
------------------------------------------------------------------- destruct H72 as [H72 H73].
exact H73.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H66.
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H66.
---------------------------------------------------------------- exact H30.
---------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H68.
----------------------------------------------------------------- exact H67.
----------------------------------------------------------------- destruct H68 as [H68 H69].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H65).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E C) as H67.
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H67.
----------------------------------------------------------------- exact H30.
----------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H69.
------------------------------------------------------------------ exact H68.
------------------------------------------------------------------ destruct H69 as [H69 H70].
apply (@euclidean__tactics.not__nCol__Col (B) (E) (C)).
-------------------------------------------------------------------intro H71.
apply (@euclidean__tactics.Col__nCol__False (B) (E) (C) (H71)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (E) (C) (H62) (H64) H66).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C B) as H68.
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H68.
------------------------------------------------------------------ exact H30.
------------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H70.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H72.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (C) H67).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H73.
--------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
exact H75.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H69.
------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H7.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E C A) as H70.
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H70.
-------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H72.
--------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H74.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H69).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H75.
----------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H77.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H79.
------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H81.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H77.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H71.
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H71.
--------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H73.
---------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F B))) as H75.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (E) (B) H54).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F B))) as H76.
------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F B)) as H78.
------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------- destruct H78 as [H78 H79].
exact H17.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B A) as H72.
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H72.
---------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H74.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- destruct H74 as [H74 H75].
apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
------------------------------------------------------------------------intro H76.
apply (@H47).
-------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (E) (C) (F) (H67) (H57) H9).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H73.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H73.
----------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H75.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H77.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H72).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H78.
-------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H80.
--------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H82.
---------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H84.
----------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
---------------------------------------------------------------------- apply (@H22).
-----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
------------------------------------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H1) H73).


---------------------------------------------------- assert (* Cut *) (exists (H56: euclidean__axioms.Point), (euclidean__axioms.BetS D H56 E) /\ (euclidean__axioms.BetS F H56 C)) as H56.
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H56.
------------------------------------------------------ exact H30.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
apply (@euclidean__axioms.postulate__Pasch__inner (D) (F) (B) (C) (E) (H53) (H54)).
--------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (D) (B) (F) H55).

----------------------------------------------------- assert (exists H57: euclidean__axioms.Point, ((euclidean__axioms.BetS D H57 E) /\ (euclidean__axioms.BetS F H57 C))) as H58.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H58 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.BetS D H57 E) /\ (euclidean__axioms.BetS F H57 C)) as H59.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong A B C F) /\ ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C))) as H61.
-------------------------------------------------------- exact H30.
-------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA E A B E C F) /\ (euclidean__defs.CongA E B A E F C)) as H63.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- destruct H63 as [H63 H64].
assert (* Cut *) (euclidean__axioms.BetS C H57 F) as H65.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (H57) (C) H60).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C F H57) as H66.
----------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (F) (H57)).
------------------------------------------------------------left.
exact H65.

------------------------------------------------------------ exact H48.
----------------------------------------------------------- assert (* Cut *) (A = A) as H67.
------------------------------------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out C A A) as H68.
------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
--------------------------------------------------------------right.
left.
exact H67.

-------------------------------------------------------------- exact H16.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C A C H57) as H69.
-------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (B) (A) (C) (A) (C) (F) (A) (H57) (H52) (H68) H66).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C A C F) as H70.
--------------------------------------------------------------- exact H52.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E H57 D) as H71.
---------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (H57) (E) H59).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C A E) as H72.
----------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (C) (E) (A) H45).
----------------------------------------------------------------- assert (* Cut *) (D = D) as H73.
------------------------------------------------------------------ apply (@logic.eq__refl (Point) D).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D C) as H74.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D B))) as H74.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (C) (B) H53).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D B))) as H75.
--------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D B)) as H77.
---------------------------------------------------------------------- exact H76.
---------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H77.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H75.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (C) H74).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H76.
--------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (D) (D)).
----------------------------------------------------------------------right.
left.
exact H73.

---------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C A C H57) as H77.
---------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C A C D) as H78.
----------------------------------------------------------------------- exists E.
exists H57.
exists D.
split.
------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H79.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H57 D) /\ ((euclidean__axioms.neq E H57) /\ (euclidean__axioms.neq E D))) as H79.
------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H57) (D) H71).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H57 D) /\ ((euclidean__axioms.neq E H57) /\ (euclidean__axioms.neq E D))) as H80.
-------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq E H57) /\ (euclidean__axioms.neq E D)) as H82.
--------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H3.
------------------------------------------------------------------------ assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS B e C) /\ (euclidean__axioms.Cong e B e C)) as H80.
------------------------------------------------------------------------- apply (@proposition__10.proposition__10 (B) (C) H79).
------------------------------------------------------------------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS B e C) /\ (euclidean__axioms.Cong e B e C))) as H81.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- destruct H81 as [e H81].
assert (* AndElim *) ((euclidean__axioms.BetS B e C) /\ (euclidean__axioms.Cong e B e C)) as H82.
--------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* Cut *) (euclidean__axioms.Col B e C) as H84.
---------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H82.
---------------------------------------------------------------------------- assert (* Cut *) (~(A = e)) as H85.
----------------------------------------------------------------------------- intro H85.
assert (* Cut *) (euclidean__axioms.BetS B A C) as H86.
------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point e (fun A0: euclidean__axioms.Point => (euclidean__axioms.Triangle A0 B C) -> ((euclidean__axioms.nCol A0 B C) -> ((~(A0 = C)) -> ((euclidean__axioms.BetS A0 E C) -> ((euclidean__axioms.Cong E A0 E C) -> ((~(A0 = C)) -> ((euclidean__axioms.neq C A0) -> ((euclidean__axioms.BetS A0 C G) -> ((~(euclidean__axioms.Col B E A0)) -> ((euclidean__defs.CongA B E A0 C E F) -> ((~(euclidean__axioms.Col A0 E B)) -> ((euclidean__defs.CongA A0 E B B E A0) -> ((euclidean__defs.CongA A0 E B C E F) -> ((~(euclidean__axioms.Col E A0 B)) -> ((euclidean__axioms.Cong A0 B C F) -> ((euclidean__defs.CongA E A0 B E C F) -> ((euclidean__defs.CongA E B A0 E F C) -> ((~(euclidean__axioms.Col B A0 E)) -> ((euclidean__defs.Out A0 C E) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.neq B A0) -> ((euclidean__defs.Out A0 B B) -> ((~(euclidean__axioms.Col B A0 C)) -> ((euclidean__defs.CongA B A0 C B A0 C) -> ((euclidean__defs.CongA B A0 C B A0 E) -> ((euclidean__defs.CongA B A0 E E A0 B) -> ((euclidean__defs.CongA B A0 C E A0 B) -> ((euclidean__defs.CongA B A0 C E C F) -> ((euclidean__axioms.BetS C E A0) -> ((euclidean__defs.Out C E A0) -> ((euclidean__defs.CongA E C F A0 C F) -> ((euclidean__defs.CongA B A0 C A0 C F) -> ((A0 = A0) -> ((euclidean__defs.Out C A0 A0) -> ((euclidean__defs.CongA B A0 C A0 C H57) -> ((euclidean__defs.CongA B A0 C A0 C F) -> ((euclidean__defs.Out C A0 E) -> ((euclidean__defs.CongA B A0 C A0 C H57) -> ((euclidean__defs.LtA B A0 C A0 C D) -> (euclidean__axioms.BetS B A0 C))))))))))))))))))))))))))))))))))))))))) with (x := A).
-------------------------------------------------------------------------------intro H86.
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
exact H82.

------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------- exact H2.
------------------------------------------------------------------------------- exact H7.
------------------------------------------------------------------------------- exact H8.
------------------------------------------------------------------------------- exact H15.
------------------------------------------------------------------------------- exact H16.
------------------------------------------------------------------------------- exact H20.
------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------- exact H24.
------------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------------- exact H26.
------------------------------------------------------------------------------- exact H29.
------------------------------------------------------------------------------- exact H61.
------------------------------------------------------------------------------- exact H63.
------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------- exact H31.
------------------------------------------------------------------------------- exact H32.
------------------------------------------------------------------------------- exact H34.
------------------------------------------------------------------------------- exact H35.
------------------------------------------------------------------------------- exact H36.
------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------- exact H39.
------------------------------------------------------------------------------- exact H40.
------------------------------------------------------------------------------- exact H41.
------------------------------------------------------------------------------- exact H42.
------------------------------------------------------------------------------- exact H43.
------------------------------------------------------------------------------- exact H45.
------------------------------------------------------------------------------- exact H51.
------------------------------------------------------------------------------- exact H52.
------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A C) as H87.
------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H86.
------------------------------------------------------------------------------- apply (@H22).
--------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
---------------------------------------------------------------------------------intro H88.
apply (@H37 H87).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e A) as H86.
------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (e) H85).
------------------------------------------------------------------------------ assert (* Cut *) (exists (f: euclidean__axioms.Point), (euclidean__axioms.BetS A e f) /\ (euclidean__axioms.Cong e f e A)) as H87.
------------------------------------------------------------------------------- apply (@lemma__extension.lemma__extension (A) (e) (e) (A) (H85) H86).
------------------------------------------------------------------------------- assert (exists f: euclidean__axioms.Point, ((euclidean__axioms.BetS A e f) /\ (euclidean__axioms.Cong e f e A))) as H88.
-------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------- destruct H88 as [f H88].
assert (* AndElim *) ((euclidean__axioms.BetS A e f) /\ (euclidean__axioms.Cong e f e A)) as H89.
--------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* Cut *) (~(B = C)) as H91.
---------------------------------------------------------------------------------- intro H91.
assert (* Cut *) (euclidean__axioms.Col B A C) as H92.
----------------------------------------------------------------------------------- right.
left.
exact H91.
----------------------------------------------------------------------------------- apply (@H3 H91).
---------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A e B)) as H92.
----------------------------------------------------------------------------------- intro H92.
assert (* Cut *) (euclidean__axioms.Col B e C) as H93.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col e B A) as H94.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col e B A) /\ ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A B e) /\ (euclidean__axioms.Col B e A))))) as H94.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (e) (B) H92).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col e B A) /\ ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A B e) /\ (euclidean__axioms.Col B e A))))) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col e B A) /\ ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A B e) /\ (euclidean__axioms.Col B e A)))) as H97.
---------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A B e) /\ (euclidean__axioms.Col B e A))) as H99.
----------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col A B e) /\ (euclidean__axioms.Col B e A)) as H101.
------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------ destruct H101 as [H101 H102].
exact H97.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e B C) as H95.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H95.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (e) (C) H93).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H96.
---------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)))) as H98.
----------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))) as H100.
------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)) as H102.
------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H96.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B e) as H96.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H96.
---------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (e) (C) H82).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H97.
----------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C)) as H99.
------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------ destruct H99 as [H99 H100].
exact H99.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e B) as H97.
---------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (e) H96).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H98.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------------------------------------------------------------------------------------------intro H98.
apply (@H37).
-------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (e) (B) (A) (C) (H94) (H95) H97).


----------------------------------------------------------------------------------------- apply (@H22).
------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------------------------------------------------------------------intro H99.
apply (@H37 H98).


----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A e B C e f) as H93.
------------------------------------------------------------------------------------ apply (@proposition__15.proposition__15a (A) (f) (B) (C) (e) (H89) (H82)).
-------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (e) (B) H92).

------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col B e A)) as H94.
------------------------------------------------------------------------------------- intro H94.
assert (* Cut *) (euclidean__axioms.Col A e B) as H95.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e B A) /\ ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A B e) /\ ((euclidean__axioms.Col B A e) /\ (euclidean__axioms.Col A e B))))) as H95.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (e) (A) H94).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e B A) /\ ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A B e) /\ ((euclidean__axioms.Col B A e) /\ (euclidean__axioms.Col A e B))))) as H96.
---------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A B e) /\ ((euclidean__axioms.Col B A e) /\ (euclidean__axioms.Col A e B)))) as H98.
----------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col A B e) /\ ((euclidean__axioms.Col B A e) /\ (euclidean__axioms.Col A e B))) as H100.
------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------ destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col B A e) /\ (euclidean__axioms.Col A e B)) as H102.
------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H103.
-------------------------------------------------------------------------------------- apply (@H22).
---------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
----------------------------------------------------------------------------------------intro H96.
apply (@H92 H95).


------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B e A A e B) as H95.
-------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (e) (A)).
---------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (e) (A) H94).

-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B e A C e f) as H96.
--------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (e) (A) (A) (e) (B) (C) (e) (f) (H95) H93).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A e f e) as H97.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A e f e) /\ (euclidean__axioms.Cong f e A e)) as H97.
----------------------------------------------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (e) (f) (e) (A) H90).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A e f e) /\ (euclidean__axioms.Cong f e A e)) as H98.
------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
exact H98.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e A e f) as H98.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong e A e f) /\ ((euclidean__axioms.Cong e A f e) /\ (euclidean__axioms.Cong A e e f))) as H98.
------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (e) (f) (e) H97).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong e A e f) /\ ((euclidean__axioms.Cong e A f e) /\ (euclidean__axioms.Cong A e e f))) as H99.
------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Cong e A f e) /\ (euclidean__axioms.Cong A e e f)) as H101.
-------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H99.
----------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col e B A)) as H99.
------------------------------------------------------------------------------------------ intro H99.
assert (* Cut *) (euclidean__axioms.Col A e B) as H100.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B e A) /\ ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A e B) /\ ((euclidean__axioms.Col e A B) /\ (euclidean__axioms.Col A B e))))) as H100.
-------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (e) (B) (A) H99).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B e A) /\ ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A e B) /\ ((euclidean__axioms.Col e A B) /\ (euclidean__axioms.Col A B e))))) as H101.
--------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col A e B) /\ ((euclidean__axioms.Col e A B) /\ (euclidean__axioms.Col A B e)))) as H103.
---------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col A e B) /\ ((euclidean__axioms.Col e A B) /\ (euclidean__axioms.Col A B e))) as H105.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col e A B) /\ (euclidean__axioms.Col A B e)) as H107.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
exact H105.
------------------------------------------------------------------------------------------- apply (@H22).
--------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
---------------------------------------------------------------------------------------------intro H101.
apply (@H92 H100).


------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H100.
------------------------------------------------------------------------------------------- apply (@proposition__04.proposition__04 (e) (B) (A) (e) (C) (f) (H83) (H98) H96).
------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B e)) as H101.
-------------------------------------------------------------------------------------------- intro H101.
assert (* Cut *) (euclidean__axioms.Col e B A) as H102.
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H102.
---------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H104.
----------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* Cut *) ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col B e A) /\ ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A e B) /\ (euclidean__axioms.Col e B A))))) as H106.
------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (e) H101).
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A e) /\ ((euclidean__axioms.Col B e A) /\ ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A e B) /\ (euclidean__axioms.Col e B A))))) as H107.
------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col B e A) /\ ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A e B) /\ (euclidean__axioms.Col e B A)))) as H109.
-------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col e A B) /\ ((euclidean__axioms.Col A e B) /\ (euclidean__axioms.Col e B A))) as H111.
--------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col A e B) /\ (euclidean__axioms.Col e B A)) as H113.
---------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
exact H114.
--------------------------------------------------------------------------------------------- apply (@H22).
----------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-----------------------------------------------------------------------------------------------intro H103.
apply (@H99 H102).


-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C e) as H102.
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H102.
---------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H104.
----------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
apply (@lemma__ray4.lemma__ray4 (B) (C) (e)).
------------------------------------------------------------------------------------------------left.
exact H82.

------------------------------------------------------------------------------------------------ exact H91.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H103.
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H103.
----------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H105.
------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------------------------------------------------------------------------------------right.
left.
exact H67.

------------------------------------------------------------------------------------------------- exact H35.
---------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H104.
----------------------------------------------------------------------------------------------- intro H104.
assert (* Cut *) (euclidean__axioms.Col B A C) as H105.
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H105.
------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H109.
--------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H104).
--------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H110.
---------------------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H112.
----------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H114.
------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H116.
------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H110.
------------------------------------------------------------------------------------------------ apply (@H22).
-------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
--------------------------------------------------------------------------------------------------intro H106.
apply (@H37 H105).


----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H105.
------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H105.
------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H1).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C A B e) as H106.
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H106.
-------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H108.
--------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (A) (B) (C) (A) (e) (H105) (H103) H102).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B e e B A) as H107.
-------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H107.
--------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H109.
---------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (e)).
-----------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (A) (B) (e) H101).

-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C e B A) as H108.
--------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H108.
---------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H110.
----------------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (A) (B) (e) (e) (B) (A) (H106) H107).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C e C f) as H109.
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H109.
----------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H111.
------------------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------------------ destruct H111 as [H111 H112].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (e) (B) (A) (e) (C) (f) (H108) H111).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C e B) as H110.
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H110.
------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H112.
------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (e) (C) H82).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H111.
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H111.
------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H113.
-------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* Cut *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H115.
--------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (e) (B) H110).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H118.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out C e B) as H112.
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H112.
-------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
apply (@lemma__ray4.lemma__ray4 (C) (e) (B)).
----------------------------------------------------------------------------------------------------------right.
right.
exact H110.

---------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (f = f) as H113.
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H113.
--------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H115.
---------------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
apply (@logic.eq__refl (Point) f).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol e C f) as H114.
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H114.
---------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H116.
----------------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
apply (@euclidean__tactics.nCol__notCol (e) (C) (f)).
------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (e) (C) (f)).
-------------------------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (e) (C) (f) H109).


--------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(C = f)) as H115.
---------------------------------------------------------------------------------------------------------- intro H115.
assert (* Cut *) (euclidean__axioms.Col e C f) as H116.
----------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H115.
----------------------------------------------------------------------------------------------------------- apply (@H22).
------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------------------------------------------------------------------------------------intro H117.
apply (@euclidean__tactics.Col__nCol__False (e) (C) (f) (H114) H116).


---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C f f) as H116.
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H116.
------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H118.
------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
apply (@lemma__ray4.lemma__ray4 (C) (f) (f)).
--------------------------------------------------------------------------------------------------------------right.
left.
exact H113.

-------------------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col e C f)) as H117.
------------------------------------------------------------------------------------------------------------ intro H117.
assert (* Cut *) (euclidean__axioms.Col A e f) as H118.
------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H89.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f e A) as H119.
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H119.
--------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H121.
---------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* Cut *) ((euclidean__axioms.Col e A f) /\ ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))))) as H123.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (e) (f) H118).
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e A f) /\ ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))))) as H124.
------------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A)))) as H126.
------------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))) as H128.
-------------------------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A)) as H130.
--------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
exact H131.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f e C) as H120.
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H120.
---------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H122.
----------------------------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* Cut *) ((euclidean__axioms.Col C e f) /\ ((euclidean__axioms.Col C f e) /\ ((euclidean__axioms.Col f e C) /\ ((euclidean__axioms.Col e f C) /\ (euclidean__axioms.Col f C e))))) as H124.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (e) (C) (f) H117).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C e f) /\ ((euclidean__axioms.Col C f e) /\ ((euclidean__axioms.Col f e C) /\ ((euclidean__axioms.Col e f C) /\ (euclidean__axioms.Col f C e))))) as H125.
------------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col C f e) /\ ((euclidean__axioms.Col f e C) /\ ((euclidean__axioms.Col e f C) /\ (euclidean__axioms.Col f C e)))) as H127.
-------------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col f e C) /\ ((euclidean__axioms.Col e f C) /\ (euclidean__axioms.Col f C e))) as H129.
--------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col e f C) /\ (euclidean__axioms.Col f C e)) as H131.
---------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
exact H129.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e f) as H121.
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H121.
----------------------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H123.
------------------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
assert (* Cut *) ((euclidean__axioms.neq e f) /\ ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f))) as H125.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (e) (f) H89).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e f) /\ ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f))) as H126.
-------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f)) as H128.
--------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H126.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq f e) as H122.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H122.
------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H124.
------------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (e) (f) H121).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e A C) as H123.
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H123.
------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H125.
-------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
apply (@euclidean__tactics.not__nCol__Col (e) (A) (C)).
---------------------------------------------------------------------------------------------------------------------intro H127.
apply (@euclidean__tactics.Col__nCol__False (e) (A) (C) (H127)).
----------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (f) (e) (A) (C) (H119) (H120) H122).


------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col e C A) as H124.
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H124.
-------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H126.
--------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* Cut *) ((euclidean__axioms.Col A e C) /\ ((euclidean__axioms.Col A C e) /\ ((euclidean__axioms.Col C e A) /\ ((euclidean__axioms.Col e C A) /\ (euclidean__axioms.Col C A e))))) as H128.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (e) (A) (C) H123).
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A e C) /\ ((euclidean__axioms.Col A C e) /\ ((euclidean__axioms.Col C e A) /\ ((euclidean__axioms.Col e C A) /\ (euclidean__axioms.Col C A e))))) as H129.
----------------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col A C e) /\ ((euclidean__axioms.Col C e A) /\ ((euclidean__axioms.Col e C A) /\ (euclidean__axioms.Col C A e)))) as H131.
------------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col C e A) /\ ((euclidean__axioms.Col e C A) /\ (euclidean__axioms.Col C A e))) as H133.
------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col e C A) /\ (euclidean__axioms.Col C A e)) as H135.
-------------------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
exact H135.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C B) as H125.
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H125.
--------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H127.
---------------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* Cut *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H129.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (e) (C) H84).
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H130.
------------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)))) as H132.
------------------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))) as H134.
-------------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)) as H136.
--------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H132.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e C) as H126.
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H126.
---------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* Cut *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H130.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (e) (C) H82).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H131.
------------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C)) as H133.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H131.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H127.
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H127.
----------------------------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H129.
------------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------------ destruct H129 as [H129 H130].
apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
-------------------------------------------------------------------------------------------------------------------------intro H131.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H131)).
--------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (e) (C) (A) (B) (H124) (H125) H126).


---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H128.
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H128.
------------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H130.
------------------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H132.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H127).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H133.
--------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H135.
---------------------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H137.
----------------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H139.
------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
exact H140.
----------------------------------------------------------------------------------------------------------------------- apply (@H22).
------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------------------------------------------------------------------------------------------------intro H129.
apply (@H37 H128).


------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA e C f e C f) as H118.
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H118.
-------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H120.
--------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (e) (C) (f) H114).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA e C f B C f) as H119.
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H119.
--------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H121.
---------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (e) (C) (f) (e) (C) (f) (B) (f) (H118) (H112) H116).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C B C f) as H120.
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H120.
---------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H122.
----------------------------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (e) (C) (f) (B) (C) (f) (H109) H119).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G C A) as H121.
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H121.
----------------------------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H123.
------------------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------------------ destruct H123 as [H123 H124].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (C) (G) H20).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H122.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H122.
------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H124.
------------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq G C) /\ (euclidean__axioms.neq G A))) as H126.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (C) (A) H121).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq G C) /\ (euclidean__axioms.neq G A))) as H127.
--------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ (euclidean__axioms.neq G A)) as H129.
---------------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H129.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H123.
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H123.
------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H125.
-------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (C) H122).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS f e A) as H124.
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H124.
-------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H126.
--------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (e) (f) H89).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col G A f)) as H125.
-------------------------------------------------------------------------------------------------------------------- intro H125.
assert (* Cut *) (euclidean__axioms.Col f A G) as H126.
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H126.
---------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* Cut *) ((euclidean__axioms.Col A G f) /\ ((euclidean__axioms.Col A f G) /\ ((euclidean__axioms.Col f G A) /\ ((euclidean__axioms.Col G f A) /\ (euclidean__axioms.Col f A G))))) as H130.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (f) H125).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A G f) /\ ((euclidean__axioms.Col A f G) /\ ((euclidean__axioms.Col f G A) /\ ((euclidean__axioms.Col G f A) /\ (euclidean__axioms.Col f A G))))) as H131.
------------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col A f G) /\ ((euclidean__axioms.Col f G A) /\ ((euclidean__axioms.Col G f A) /\ (euclidean__axioms.Col f A G)))) as H133.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col f G A) /\ ((euclidean__axioms.Col G f A) /\ (euclidean__axioms.Col f A G))) as H135.
--------------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col G f A) /\ (euclidean__axioms.Col f A G)) as H137.
---------------------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H138.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A e f) as H127.
---------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H89.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f A e) as H128.
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H128.
------------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H130.
------------------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* Cut *) ((euclidean__axioms.Col e A f) /\ ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))))) as H132.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (e) (f) H127).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e A f) /\ ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))))) as H133.
--------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col e f A) /\ ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A)))) as H135.
---------------------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col f A e) /\ ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A))) as H137.
----------------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col A f e) /\ (euclidean__axioms.Col f e A)) as H139.
------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
exact H137.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A f) as H129.
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H129.
------------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H131.
-------------------------------------------------------------------------------------------------------------------------- exact H130.
-------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* Cut *) ((euclidean__axioms.neq e f) /\ ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f))) as H133.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (e) (f) H89).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e f) /\ ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f))) as H134.
---------------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq A e) /\ (euclidean__axioms.neq A f)) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H137.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq f A) as H130.
------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H130.
-------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H132.
--------------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (f) H129).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G e) as H131.
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H131.
--------------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H133.
---------------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
apply (@euclidean__tactics.not__nCol__Col (A) (G) (e)).
-----------------------------------------------------------------------------------------------------------------------------intro H135.
apply (@euclidean__tactics.Col__nCol__False (A) (G) (e) (H135)).
------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (f) (A) (G) (e) (H126) (H128) H130).


-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A e) as H132.
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H132.
---------------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H134.
----------------------------------------------------------------------------------------------------------------------------- exact H133.
----------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* Cut *) ((euclidean__axioms.Col G A e) /\ ((euclidean__axioms.Col G e A) /\ ((euclidean__axioms.Col e A G) /\ ((euclidean__axioms.Col A e G) /\ (euclidean__axioms.Col e G A))))) as H136.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (e) H131).
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G A e) /\ ((euclidean__axioms.Col G e A) /\ ((euclidean__axioms.Col e A G) /\ ((euclidean__axioms.Col A e G) /\ (euclidean__axioms.Col e G A))))) as H137.
------------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col G e A) /\ ((euclidean__axioms.Col e A G) /\ ((euclidean__axioms.Col A e G) /\ (euclidean__axioms.Col e G A)))) as H139.
-------------------------------------------------------------------------------------------------------------------------------- exact H138.
-------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col e A G) /\ ((euclidean__axioms.Col A e G) /\ (euclidean__axioms.Col e G A))) as H141.
--------------------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col A e G) /\ (euclidean__axioms.Col e G A)) as H143.
---------------------------------------------------------------------------------------------------------------------------------- exact H142.
---------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
exact H137.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C G) as H133.
---------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H20.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A C) as H134.
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H134.
------------------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H136.
------------------------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* Cut *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H138.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (G) H133).
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H139.
--------------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)))) as H141.
---------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))) as H143.
----------------------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)) as H145.
------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
exact H143.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A G) as H135.
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H135.
------------------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H137.
-------------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* Cut *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A G))) as H139.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (C) (G) H20).
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A G))) as H140.
---------------------------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A G)) as H142.
----------------------------------------------------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
exact H143.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G A) as H136.
------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H136.
-------------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H138.
--------------------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H135).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A e C) as H137.
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H137.
--------------------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H139.
---------------------------------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
apply (@euclidean__tactics.not__nCol__Col (A) (e) (C)).
-----------------------------------------------------------------------------------------------------------------------------------intro H141.
apply (@euclidean__tactics.Col__nCol__False (A) (e) (C) (H141)).
------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (A) (e) (C) (H132) (H134) H136).


-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C A) as H138.
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H138.
---------------------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H140.
----------------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* Cut *) ((euclidean__axioms.Col e A C) /\ ((euclidean__axioms.Col e C A) /\ ((euclidean__axioms.Col C A e) /\ ((euclidean__axioms.Col A C e) /\ (euclidean__axioms.Col C e A))))) as H142.
------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (e) (C) H137).
------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col e A C) /\ ((euclidean__axioms.Col e C A) /\ ((euclidean__axioms.Col C A e) /\ ((euclidean__axioms.Col A C e) /\ (euclidean__axioms.Col C e A))))) as H143.
------------------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col e C A) /\ ((euclidean__axioms.Col C A e) /\ ((euclidean__axioms.Col A C e) /\ (euclidean__axioms.Col C e A)))) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Col C A e) /\ ((euclidean__axioms.Col A C e) /\ (euclidean__axioms.Col C e A))) as H147.
--------------------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col A C e) /\ (euclidean__axioms.Col C e A)) as H149.
---------------------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
exact H145.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B e C) as H139.
---------------------------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C B) as H140.
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H140.
------------------------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H142.
------------------------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* Cut *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H144.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (e) (C) H139).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e B C) /\ ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))))) as H145.
--------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Col e C B) /\ ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)))) as H147.
---------------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col C B e) /\ ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B))) as H149.
----------------------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Col B C e) /\ (euclidean__axioms.Col C e B)) as H151.
------------------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H151 H152].
exact H147.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e C) as H141.
------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H141.
------------------------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H143.
-------------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* Cut *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H145.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (e) (C) H82).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C))) as H146.
---------------------------------------------------------------------------------------------------------------------------------------- exact H145.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq B e) /\ (euclidean__axioms.neq B C)) as H148.
----------------------------------------------------------------------------------------------------------------------------------------- exact H147.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
exact H146.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C A B) as H142.
------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H142.
-------------------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H144.
--------------------------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
----------------------------------------------------------------------------------------------------------------------------------------intro H146.
apply (@H117).
-----------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (e) (C) (f) (H137) (H127) H85).


------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H143.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H143.
--------------------------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H145.
---------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H147.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H142).
----------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H148.
------------------------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H150.
------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H152.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H154.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
exact H150.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@H22).
---------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
----------------------------------------------------------------------------------------------------------------------------------------intro H144.
apply (@H104 H143).


-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (h: euclidean__axioms.Point), (euclidean__axioms.BetS G h e) /\ (euclidean__axioms.BetS f h C)) as H126.
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H126.
---------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
apply (@euclidean__axioms.postulate__Pasch__inner (G) (f) (A) (C) (e) (H121) (H124)).
------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (G) (A) (f) H125).

--------------------------------------------------------------------------------------------------------------------- assert (exists h: euclidean__axioms.Point, ((euclidean__axioms.BetS G h e) /\ (euclidean__axioms.BetS f h C))) as H127.
---------------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------------- destruct H127 as [h H127].
assert (* AndElim *) ((euclidean__axioms.BetS G h e) /\ (euclidean__axioms.BetS f h C)) as H128.
----------------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Cong B A C f) /\ ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C))) as H130.
------------------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__defs.CongA e B A e C f) /\ (euclidean__defs.CongA e A B e f C)) as H132.
------------------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* Cut *) (euclidean__axioms.BetS C h f) as H134.
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (f) (h) (C) H129).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq h C) as H135.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq h C) /\ ((euclidean__axioms.neq f h) /\ (euclidean__axioms.neq f C))) as H135.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (f) (h) (C) H129).
---------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq h C) /\ ((euclidean__axioms.neq f h) /\ (euclidean__axioms.neq f C))) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq f h) /\ (euclidean__axioms.neq f C)) as H138.
------------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
exact H136.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C h) as H136.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (h) (C) H135).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C h f) as H137.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (h) (f)).
------------------------------------------------------------------------------------------------------------------------------right.
right.
exact H134.

------------------------------------------------------------------------------------------------------------------------------ exact H136.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C f h) as H138.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 (C) (h) (f) H137).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out C B B) as H139.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
--------------------------------------------------------------------------------------------------------------------------------right.
left.
exact H33.

-------------------------------------------------------------------------------------------------------------------------------- exact H4.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C B C h) as H140.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (B) (C) (f) (B) (h) (H120) (H139) H138).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C B C f) as H141.
--------------------------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e h G) as H142.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (h) (e) H128).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C e B) as H143.
----------------------------------------------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C e B) as H144.
------------------------------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out C B e) as H145.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (C) (e) (B) H144).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (G = G) as H146.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) G).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C G G) as H147.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (G) (G)).
----------------------------------------------------------------------------------------------------------------------------------------right.
left.
exact H146.

---------------------------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C B C h) as H148.
---------------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C B C G) as H149.
----------------------------------------------------------------------------------------------------------------------------------------- exists e.
exists h.
exists G.
split.
------------------------------------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H147.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col G C B)) as H150.
------------------------------------------------------------------------------------------------------------------------------------------ intro H150.
assert (* Cut *) (euclidean__axioms.Col A C G) as H151.
------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H20.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C A) as H152.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H152.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (G) H151).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))))) as H153.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)))) as H155.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Col G A C) /\ ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A))) as H157.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col A G C) /\ (euclidean__axioms.Col G C A)) as H159.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
exact H160.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H153.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H153.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (e) (B) H143).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H154.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B)) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
exact H123.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H154.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B A) as H155.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
------------------------------------------------------------------------------------------------------------------------------------------------intro H155.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (A) (H155)).
-------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (C) (B) (A) (H150) (H152) H154).


----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H155).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H157.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H161.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H163.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
exact H164.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@H22).
-------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
--------------------------------------------------------------------------------------------------------------------------------------------------intro H157.
apply (@H104 H156).


------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA G C B D C A) as H151.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__15.proposition__15a (G) (A) (B) (D) (C) (H121) (H0)).
--------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (G) (C) (B) H150).

------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A C D)) as H152.
-------------------------------------------------------------------------------------------------------------------------------------------- intro H152.
assert (* Cut *) (euclidean__axioms.Col D C A) as H153.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H153.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (D) H152).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H154.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))) as H158.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)) as H160.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
exact H161.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H154.
---------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H0.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H155.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H155.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H154).
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H158.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H160.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H162.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
exact H163.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (e) (B) H143).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e B) /\ ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B))) as H157.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq C e) /\ (euclidean__axioms.neq C B)) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
exact H75.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D C) as H157.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H158.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
---------------------------------------------------------------------------------------------------------------------------------------------------intro H158.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H158)).
----------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (A) (B) (H153) (H155) H157).


-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H159.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H158).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H160.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H162.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H166.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
exact H162.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H22).
----------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-----------------------------------------------------------------------------------------------------------------------------------------------------intro H160.
apply (@H104 H159).


-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G C B B C G) as H153.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (G) (C) (B)).
----------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (G) (C) (B) H150).

--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C G C B) as H154.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (B) (C) (G) (G) (C) (B) (H149) H153).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D C A)) as H155.
----------------------------------------------------------------------------------------------------------------------------------------------- intro H155.
assert (* Cut *) (euclidean__axioms.Col A C D) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (A) H155).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))))) as H157.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)))) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D))) as H161.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ (euclidean__axioms.Col A C D)) as H163.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
exact H164.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@H22).
-------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
--------------------------------------------------------------------------------------------------------------------------------------------------intro H157.
apply (@H152 H156).


----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D C A A C D) as H156.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (D) (C) (A)).
-------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (D) (C) (A) H155).

------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA G C B A C D) as H157.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (C) (B) (D) (C) (A) (A) (C) (D) (H151) H156).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C D G C B) as H158.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (G) (C) (B) (A) (C) (D) H157).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C A C D) as H159.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (G) (C) (B) (A) (C) (D) (H154) H158).
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H160.
---------------------------------------------------------------------------------------------------------------------------------------------------- intro H160.
assert (* Cut *) (euclidean__axioms.Col A B C) as H161.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H161.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H160).
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H162.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H164.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H166.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H168.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
exact H169.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H22).
------------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (E) (A)).
-------------------------------------------------------------------------------------------------------------------------------------------------------intro H162.
apply (@H104 H161).


---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H161.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (B) (A)).
------------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H160).

----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA C B A A C D) as H162.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (B) (C) (A) (C) (D) (C) (B) (A) (H159) H161).
------------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
Qed.
