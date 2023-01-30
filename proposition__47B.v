Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__8__2.
Require Export lemma__8__7.
Require Export lemma__ABCequalsCBA.
Require Export lemma__Euclid4.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__angleaddition.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__diagonalsbisect.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesideflip.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__righttogether.
Require Export lemma__samesidesymmetric.
Require Export lemma__squareparallelogram.
Require Export logic.
Require Export proposition__04.
Require Export proposition__34.
Require Export proposition__41.
Require Export proposition__47A.
Definition proposition__47B : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Per B A C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.TS D C B A) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__defs.PG B X Y D) /\ ((euclidean__axioms.BetS B X C) /\ ((euclidean__defs.PG X C E Y) /\ ((euclidean__axioms.BetS D Y E) /\ ((euclidean__axioms.BetS Y X A) /\ ((euclidean__defs.Per D Y A) /\ (euclidean__axioms.EF A B F G B X Y D)))))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (exists (M: euclidean__axioms.Point) (L: euclidean__axioms.Point), (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A)))))) as H5.
- apply (@proposition__47A.proposition__47A (A) (B) (C) (D) (E) (H) (H0) (H3) H4).
- assert (exists M: euclidean__axioms.Point, (exists (L: euclidean__axioms.Point), (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A))))))) as H6.
-- exact H5.
-- destruct H6 as [M H6].
assert (exists L: euclidean__axioms.Point, ((euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A))))))) as H7.
--- exact H6.
--- destruct H7 as [L H7].
assert (* AndElim *) ((euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A)))))) as H8.
---- exact H7.
---- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A))))) as H10.
----- exact H9.
----- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A)))) as H12.
------ exact H11.
------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A))) as H14.
------- exact H13.
------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A)) as H16.
-------- exact H15.
-------- destruct H16 as [H16 H17].
assert (* Cut *) (exists (N: euclidean__axioms.Point), (euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D))) as H18.
--------- exact H4.
--------- assert (exists N: euclidean__axioms.Point, ((euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D)))) as H19.
---------- exact H18.
---------- destruct H19 as [N H19].
assert (* AndElim *) ((euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D))) as H20.
----------- exact H19.
----------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D)) as H22.
------------ exact H21.
------------ destruct H22 as [H22 H23].
assert (* Cut *) (euclidean__defs.Per G A B) as H24.
------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H24.
-------------- exact H3.
-------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H26.
--------------- exact H25.
--------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H28.
---------------- exact H27.
---------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H30.
----------------- exact H29.
----------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H32.
------------------ exact H31.
------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H34.
------------------- exact H33.
------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H36.
-------------------- exact H1.
-------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H38.
--------------------- exact H37.
--------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H40.
---------------------- exact H39.
---------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H42.
----------------------- exact H41.
----------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H44.
------------------------ exact H43.
------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H46.
------------------------- exact H45.
------------------------- destruct H46 as [H46 H47].
exact H42.
------------- assert (* Cut *) (euclidean__axioms.BetS G A C) as H25.
-------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (G0: euclidean__axioms.Point), (euclidean__defs.Per G0 A0 B0) -> ((euclidean__defs.Per B0 A0 C0) -> ((euclidean__axioms.TS G0 B0 A0 C0) -> (euclidean__axioms.BetS G0 A0 C0)))) as H25.
--------------- intro A0.
intro B0.
intro C0.
intro G0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.RT G0 A0 B0 B0 A0 C0) /\ (euclidean__axioms.BetS G0 A0 C0)) as __2.
---------------- apply (@lemma__righttogether.lemma__righttogether (A0) (B0) (C0) (G0) (__) (__0) __1).
---------------- destruct __2 as [__2 __3].
exact __3.
--------------- apply (@H25 (A) (B) (C) (G) (H24) (H0) H2).
-------------- assert (* Cut *) (euclidean__defs.Per A B F) as H26.
--------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H26.
---------------- exact H3.
---------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H28.
----------------- exact H27.
----------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H30.
------------------ exact H29.
------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H32.
------------------- exact H31.
------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H34.
-------------------- exact H33.
-------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H36.
--------------------- exact H35.
--------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H38.
---------------------- exact H1.
---------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H40.
----------------------- exact H39.
----------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H42.
------------------------ exact H41.
------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H44.
------------------------- exact H43.
------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H46.
-------------------------- exact H45.
-------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H48.
--------------------------- exact H47.
--------------------------- destruct H48 as [H48 H49].
exact H46.
--------------- assert (* Cut *) (euclidean__defs.Per F B A) as H27.
---------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (F) H26).
---------------- assert (* Cut *) (euclidean__defs.Per D B C) as H28.
----------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H28.
------------------ exact H3.
------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H30.
------------------- exact H29.
------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H32.
-------------------- exact H31.
-------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H34.
--------------------- exact H33.
--------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H36.
---------------------- exact H35.
---------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H38.
----------------------- exact H37.
----------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H40.
------------------------ exact H1.
------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H42.
------------------------- exact H41.
------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H44.
-------------------------- exact H43.
-------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H46.
--------------------------- exact H45.
--------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H48.
---------------------------- exact H47.
---------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H50.
----------------------------- exact H49.
----------------------------- destruct H50 as [H50 H51].
exact H34.
----------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H29.
------------------ exact H.
------------------ assert (* Cut *) (euclidean__defs.PG A B F G) as H30.
------------------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (A) (B) (F) (G) H1).
------------------- assert (* Cut *) (euclidean__defs.Par A B F G) as H31.
-------------------- assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H33.
---------------------- exact H12.
---------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H35.
----------------------- exact H8.
----------------------- destruct H35 as [H35 H36].
exact H31.
-------------------- assert (* Cut *) (euclidean__defs.Par A B G F) as H32.
--------------------- assert (* Cut *) ((euclidean__defs.Par B A F G) /\ ((euclidean__defs.Par A B G F) /\ (euclidean__defs.Par B A G F))) as H32.
---------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (F) (G) H31).
---------------------- assert (* AndElim *) ((euclidean__defs.Par B A F G) /\ ((euclidean__defs.Par A B G F) /\ (euclidean__defs.Par B A G F))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Par A B G F) /\ (euclidean__defs.Par B A G F)) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
exact H35.
--------------------- assert (* Cut *) (euclidean__defs.TP A B G F) as H33.
---------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (A) (B) (G) (F) H32).
---------------------- assert (* Cut *) (euclidean__defs.OS G F A B) as H34.
----------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((~(euclidean__defs.Meet A B G F)) /\ (euclidean__defs.OS G F A B)))) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((~(euclidean__defs.Meet A B G F)) /\ (euclidean__defs.OS G F A B))) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((~(euclidean__defs.Meet A B G F)) /\ (euclidean__defs.OS G F A B)) as H38.
-------------------------- exact H37.
-------------------------- destruct H38 as [H38 H39].
exact H39.
----------------------- assert (* Cut *) (euclidean__defs.OS F G A B) as H35.
------------------------ assert (* Cut *) ((euclidean__defs.OS F G A B) /\ ((euclidean__defs.OS G F B A) /\ (euclidean__defs.OS F G B A))) as H35.
------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (G) (F) H34).
------------------------- assert (* AndElim *) ((euclidean__defs.OS F G A B) /\ ((euclidean__defs.OS G F B A) /\ (euclidean__defs.OS F G B A))) as H36.
-------------------------- exact H35.
-------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.OS G F B A) /\ (euclidean__defs.OS F G B A)) as H38.
--------------------------- exact H37.
--------------------------- destruct H38 as [H38 H39].
exact H36.
------------------------ assert (* Cut *) (euclidean__axioms.TS G A B C) as H36.
------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip (B) (A) (G) (C) H2).
------------------------- assert (* Cut *) (euclidean__axioms.TS F A B C) as H37.
-------------------------- apply (@lemma__planeseparation.lemma__planeseparation (A) (B) (F) (G) (C) (H35) H36).
-------------------------- assert (* Cut *) (exists (a: euclidean__axioms.Point), (euclidean__axioms.BetS F a C) /\ ((euclidean__axioms.Col A B a) /\ (euclidean__axioms.nCol A B F))) as H38.
--------------------------- exact H37.
--------------------------- assert (exists a: euclidean__axioms.Point, ((euclidean__axioms.BetS F a C) /\ ((euclidean__axioms.Col A B a) /\ (euclidean__axioms.nCol A B F)))) as H39.
---------------------------- exact H38.
---------------------------- destruct H39 as [a H39].
assert (* AndElim *) ((euclidean__axioms.BetS F a C) /\ ((euclidean__axioms.Col A B a) /\ (euclidean__axioms.nCol A B F))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ (euclidean__axioms.nCol A B F)) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__axioms.Col B A a) as H44.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H44.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (a) H42).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H45.
--------------------------------- exact H44.
--------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A)))) as H47.
---------------------------------- exact H46.
---------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))) as H49.
----------------------------------- exact H48.
----------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A)) as H51.
------------------------------------ exact H50.
------------------------------------ destruct H51 as [H51 H52].
exact H45.
------------------------------- assert (* Cut *) (euclidean__defs.Par A G B F) as H45.
-------------------------------- assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H45.
--------------------------------- exact H30.
--------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H47.
---------------------------------- exact H12.
---------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H49.
----------------------------------- exact H8.
----------------------------------- destruct H49 as [H49 H50].
exact H46.
-------------------------------- assert (* Cut *) (euclidean__defs.Par A G F B) as H46.
--------------------------------- assert (* Cut *) ((euclidean__defs.Par G A B F) /\ ((euclidean__defs.Par A G F B) /\ (euclidean__defs.Par G A F B))) as H46.
---------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (G) (B) (F) H45).
---------------------------------- assert (* AndElim *) ((euclidean__defs.Par G A B F) /\ ((euclidean__defs.Par A G F B) /\ (euclidean__defs.Par G A F B))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Par A G F B) /\ (euclidean__defs.Par G A F B)) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
exact H49.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col G A C) as H47.
---------------------------------- right.
right.
right.
right.
left.
exact H25.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col A G C) as H48.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H48.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (C) H47).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H49.
------------------------------------- exact H48.
------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G)))) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))) as H53.
--------------------------------------- exact H52.
--------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G)) as H55.
---------------------------------------- exact H54.
---------------------------------------- destruct H55 as [H55 H56].
exact H49.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H49.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G C))) as H49.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (A) (C) H25).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G C))) as H50.
-------------------------------------- exact H49.
-------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G C)) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
exact H53.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C G) as H50.
------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (C) H49).
------------------------------------- assert (* Cut *) (euclidean__defs.Par F B A G) as H51.
-------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (G) (F) (B) H46).
-------------------------------------- assert (* Cut *) (euclidean__defs.Par F B C G) as H52.
--------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (F) (B) (C) (A) (G) (H51) (H48) H50).
--------------------------------------- assert (* Cut *) (euclidean__defs.Par F B G C) as H53.
---------------------------------------- assert (* Cut *) ((euclidean__defs.Par B F C G) /\ ((euclidean__defs.Par F B G C) /\ (euclidean__defs.Par B F G C))) as H53.
----------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (F) (B) (C) (G) H52).
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B F C G) /\ ((euclidean__defs.Par F B G C) /\ (euclidean__defs.Par B F G C))) as H54.
------------------------------------------ exact H53.
------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__defs.Par F B G C) /\ (euclidean__defs.Par B F G C)) as H56.
------------------------------------------- exact H55.
------------------------------------------- destruct H56 as [H56 H57].
exact H56.
---------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet F B G C)) as H54.
----------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H54.
------------------------------------------ exact H53.
------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------------------------------- exact H54.
------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H55.
-------------------------------------------- exact __TmpHyp.
-------------------------------------------- destruct H55 as [x H55].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H56.
--------------------------------------------- exact H55.
--------------------------------------------- destruct H56 as [x0 H56].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H57.
---------------------------------------------- exact H56.
---------------------------------------------- destruct H57 as [x1 H57].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H58.
----------------------------------------------- exact H57.
----------------------------------------------- destruct H58 as [x2 H58].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H59.
------------------------------------------------ exact H58.
------------------------------------------------ destruct H59 as [x3 H59].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H60.
------------------------------------------------- exact H59.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H62.
-------------------------------------------------- exact H61.
-------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col F B x) /\ ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H64.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col F B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H66.
---------------------------------------------------- exact H65.
---------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H68.
----------------------------------------------------- exact H67.
----------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col G C x1) /\ ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H70.
------------------------------------------------------ exact H69.
------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col G C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H72.
------------------------------------------------------- exact H71.
------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H74.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H76.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H78.
---------------------------------------------------------- exact H77.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80.
----------------------------------------------------------- exact H52.
----------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------ exact H80.
------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H81.
------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------- destruct H81 as [x4 H81].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
-------------------------------------------------------------- exact H81.
-------------------------------------------------------------- destruct H82 as [x5 H82].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H83.
--------------------------------------------------------------- exact H82.
--------------------------------------------------------------- destruct H83 as [x6 H83].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H84.
---------------------------------------------------------------- exact H83.
---------------------------------------------------------------- destruct H84 as [x7 H84].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H85.
----------------------------------------------------------------- exact H84.
----------------------------------------------------------------- destruct H85 as [x8 H85].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H86.
------------------------------------------------------------------ exact H85.
------------------------------------------------------------------ destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H88.
------------------------------------------------------------------- exact H87.
------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col F B x4) /\ ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H90.
-------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col F B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H92.
--------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H94.
---------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col C G x6) /\ ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H96.
----------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col C G x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H98.
------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------ destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H100.
------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H102.
-------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H104.
--------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H106.
---------------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H107.
------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------ destruct H107 as [x9 H107].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H108.
------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------- destruct H108 as [x10 H108].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H109.
-------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------- destruct H109 as [x11 H109].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H110.
--------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------- destruct H110 as [x12 H110].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H111.
---------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------- destruct H111 as [x13 H111].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H112.
----------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H114.
------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col F B x9) /\ ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H116.
------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col F B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H118.
-------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H120.
--------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H122.
---------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H124.
----------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H126.
------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
assert (* AndElim *) ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H128.
------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H130.
-------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H132.
--------------------------------------------------------------------------------------------- exact H46.
--------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H133.
----------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------- destruct H133 as [x14 H133].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H134.
------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------ destruct H134 as [x15 H134].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H135.
------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------- destruct H135 as [x16 H135].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H136.
-------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------- destruct H136 as [x17 H136].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H137.
--------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------- destruct H137 as [x18 H137].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H138.
---------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H140.
----------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H142.
------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H144.
------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H146.
-------------------------------------------------------------------------------------------------------- exact H145.
-------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Col F B x16) /\ ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H148.
--------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col F B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H150.
---------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H152.
----------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H154.
------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------ destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H156.
------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H158.
-------------------------------------------------------------------------------------------------------------- exact H45.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
--------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H159.
---------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
---------------------------------------------------------------------------------------------------------------- destruct H159 as [x19 H159].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H160.
----------------------------------------------------------------------------------------------------------------- exact H159.
----------------------------------------------------------------------------------------------------------------- destruct H160 as [x20 H160].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H161.
------------------------------------------------------------------------------------------------------------------ exact H160.
------------------------------------------------------------------------------------------------------------------ destruct H161 as [x21 H161].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H162.
------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------- destruct H162 as [x22 H162].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H163.
-------------------------------------------------------------------------------------------------------------------- exact H162.
-------------------------------------------------------------------------------------------------------------------- destruct H163 as [x23 H163].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H164.
--------------------------------------------------------------------------------------------------------------------- exact H163.
--------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H166.
---------------------------------------------------------------------------------------------------------------------- exact H165.
---------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H168.
----------------------------------------------------------------------------------------------------------------------- exact H167.
----------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H170.
------------------------------------------------------------------------------------------------------------------------ exact H169.
------------------------------------------------------------------------------------------------------------------------ destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H172.
------------------------------------------------------------------------------------------------------------------------- exact H171.
------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.Col B F x21) /\ ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H174.
-------------------------------------------------------------------------------------------------------------------------- exact H173.
-------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.Col B F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H176.
--------------------------------------------------------------------------------------------------------------------------- exact H175.
--------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H178.
---------------------------------------------------------------------------------------------------------------------------- exact H177.
---------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H180.
----------------------------------------------------------------------------------------------------------------------------- exact H179.
----------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H182.
------------------------------------------------------------------------------------------------------------------------------ exact H181.
------------------------------------------------------------------------------------------------------------------------------ destruct H182 as [H182 H183].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H184.
------------------------------------------------------------------------------------------------------------------------------- exact H32.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H185.
--------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [x24 H185].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H186.
---------------------------------------------------------------------------------------------------------------------------------- exact H185.
---------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [x25 H186].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H187.
----------------------------------------------------------------------------------------------------------------------------------- exact H186.
----------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x26 H187].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H188.
------------------------------------------------------------------------------------------------------------------------------------ exact H187.
------------------------------------------------------------------------------------------------------------------------------------ destruct H188 as [x27 H188].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H189.
------------------------------------------------------------------------------------------------------------------------------------- exact H188.
------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [x28 H189].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H190.
-------------------------------------------------------------------------------------------------------------------------------------- exact H189.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H192.
--------------------------------------------------------------------------------------------------------------------------------------- exact H191.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H194.
---------------------------------------------------------------------------------------------------------------------------------------- exact H193.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H196.
----------------------------------------------------------------------------------------------------------------------------------------- exact H195.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------ exact H197.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.Col G F x26) /\ ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.Col G F x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H204.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H206.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H208.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H211.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [x29 H211].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H212.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x30 H212].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H213.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [x31 H213].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H214.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [x32 H214].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H215.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H214.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H215 as [x33 H215].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H216.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H218.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H220.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H222.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H224.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.Col F G x31) /\ ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.Col F G x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H230.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H232.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H234.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
exact H76.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq A C) as H55.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H55.
------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H29).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H56.
-------------------------------------------- exact H55.
-------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H58.
--------------------------------------------- exact H57.
--------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H60.
---------------------------------------------- exact H59.
---------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H62.
----------------------------------------------- exact H61.
----------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H64.
------------------------------------------------ exact H63.
------------------------------------------------ destruct H64 as [H64 H65].
exact H60.
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B F) as H56.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H56.
-------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (F) (B) (G) (C) H53).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H57.
--------------------------------------------- exact H56.
--------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C))) as H59.
---------------------------------------------- exact H58.
---------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)) as H61.
----------------------------------------------- exact H60.
----------------------------------------------- destruct H61 as [H61 H62].
exact H43.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F A) as H57.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H57.
--------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (F) H56).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H58.
---------------------------------------------- exact H57.
---------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A))))) as H60.
----------------------------------------------- exact H59.
----------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))) as H62.
------------------------------------------------ exact H61.
------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A))) as H64.
------------------------------------------------- exact H63.
------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)) as H66.
-------------------------------------------------- exact H65.
-------------------------------------------------- destruct H66 as [H66 H67].
exact H67.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H58.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H58.
---------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (F) H56).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H59.
----------------------------------------------- exact H58.
----------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A))))) as H61.
------------------------------------------------ exact H60.
------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))) as H63.
------------------------------------------------- exact H62.
------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A))) as H65.
-------------------------------------------------- exact H64.
-------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)) as H67.
--------------------------------------------------- exact H66.
--------------------------------------------------- destruct H67 as [H67 H68].
exact H67.
--------------------------------------------- assert (* Cut *) (B = B) as H59.
---------------------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B B) as H60.
----------------------------------------------- right.
right.
left.
exact H59.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B a A) as H61.
------------------------------------------------ apply (@lemma__collinearbetween.lemma__collinearbetween (F) (B) (G) (C) (B) (A) (a) (H60) (H47) (H58) (H49) (H58) (H55) (H54) (H40) H44).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B a) as H62.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq a A) /\ ((euclidean__axioms.neq B a) /\ (euclidean__axioms.neq B A))) as H62.
-------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (a) (A) H61).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq a A) /\ ((euclidean__axioms.neq B a) /\ (euclidean__axioms.neq B A))) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq B a) /\ (euclidean__axioms.neq B A)) as H65.
---------------------------------------------------- exact H64.
---------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B a A) as H63.
-------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (a) (A)).
---------------------------------------------------right.
right.
exact H61.

--------------------------------------------------- exact H62.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H64.
--------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (B) H58).
--------------------------------------------------- assert (* Cut *) (F = F) as H65.
---------------------------------------------------- apply (@logic.eq__refl (Point) F).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B F F) as H66.
----------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (F) (F)).
------------------------------------------------------right.
left.
exact H65.

------------------------------------------------------ exact H64.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B F) as H67.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H67.
------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (F) (B) (G) (C) H53).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H68.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C))) as H70.
--------------------------------------------------------- exact H69.
--------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)) as H72.
---------------------------------------------------------- exact H71.
---------------------------------------------------------- destruct H72 as [H72 H73].
exact H56.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F B A) as H68.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A F) /\ ((euclidean__axioms.nCol B F A) /\ ((euclidean__axioms.nCol F A B) /\ ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A))))) as H68.
-------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (F) H67).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A F) /\ ((euclidean__axioms.nCol B F A) /\ ((euclidean__axioms.nCol F A B) /\ ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A))))) as H69.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.nCol B F A) /\ ((euclidean__axioms.nCol F A B) /\ ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A)))) as H71.
---------------------------------------------------------- exact H70.
---------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol F A B) /\ ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A))) as H73.
----------------------------------------------------------- exact H72.
----------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A)) as H75.
------------------------------------------------------------ exact H74.
------------------------------------------------------------ destruct H75 as [H75 H76].
exact H76.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A F B A) as H69.
-------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (F) (B) (A) H68).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A a) as H70.
--------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (a) (A) H63).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A F B a) as H71.
---------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (B) (A) (F) (B) (A) (F) (a) (H69) (H66) H70).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H72.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H72.
------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H29).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H73.
------------------------------------------------------------- exact H72.
------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H79.
---------------------------------------------------------------- exact H78.
---------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H81.
----------------------------------------------------------------- exact H80.
----------------------------------------------------------------- destruct H81 as [H81 H82].
exact H75.
----------------------------------------------------------- assert (* Cut *) (C = C) as H73.
------------------------------------------------------------ apply (@logic.eq__refl (Point) C).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C C) as H74.
------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
--------------------------------------------------------------right.
left.
exact H73.

-------------------------------------------------------------- exact H72.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H75.
-------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H29).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C a B C) as H76.
--------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (A) (B) (C) (a) (C) (H75) (H70) H74).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.SumA F B A A B C F B C) as H77.
---------------------------------------------------------------- exists a.
split.
----------------------------------------------------------------- exact H71.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ exact H40.
---------------------------------------------------------------- assert (* Cut *) (exists (c: euclidean__axioms.Point), (euclidean__axioms.BetS D c A) /\ ((euclidean__axioms.Col C B c) /\ (euclidean__axioms.nCol C B D))) as H78.
----------------------------------------------------------------- exact H4.
----------------------------------------------------------------- assert (exists c: euclidean__axioms.Point, ((euclidean__axioms.BetS D c A) /\ ((euclidean__axioms.Col C B c) /\ (euclidean__axioms.nCol C B D)))) as H79.
------------------------------------------------------------------ exact H78.
------------------------------------------------------------------ destruct H79 as [c H79].
assert (* AndElim *) ((euclidean__axioms.BetS D c A) /\ ((euclidean__axioms.Col C B c) /\ (euclidean__axioms.nCol C B D))) as H80.
------------------------------------------------------------------- exact H79.
------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col C B c) /\ (euclidean__axioms.nCol C B D)) as H82.
-------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* Cut *) (euclidean__defs.PG B C E D) as H84.
--------------------------------------------------------------------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (B) (C) (E) (D) H3).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D C E) as H85.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H85.
----------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H87.
------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H89.
------------------------------------------------------------------------- exact H12.
------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H91.
-------------------------------------------------------------------------- exact H8.
-------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H86.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E B D) as H86.
----------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (D) (C) (E) H85).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E D B) as H87.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par E C B D) /\ ((euclidean__defs.Par C E D B) /\ (euclidean__defs.Par E C D B))) as H87.
------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (C) (E) (B) (D) H86).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E C B D) /\ ((euclidean__defs.Par C E D B) /\ (euclidean__defs.Par E C D B))) as H88.
-------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.Par C E D B) /\ (euclidean__defs.Par E C D B)) as H90.
--------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H90.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C c) as H88.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C c) /\ ((euclidean__axioms.Col B c C) /\ ((euclidean__axioms.Col c C B) /\ ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C))))) as H88.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (c) H82).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C c) /\ ((euclidean__axioms.Col B c C) /\ ((euclidean__axioms.Col c C B) /\ ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C))))) as H89.
--------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col B c C) /\ ((euclidean__axioms.Col c C B) /\ ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C)))) as H91.
---------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col c C B) /\ ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C))) as H93.
----------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C)) as H95.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ destruct H95 as [H95 H96].
exact H89.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M C) as H89.
-------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H10.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H90.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H90.
---------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (C) H89).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)))) as H93.
------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))) as H95.
------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)) as H97.
-------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H95.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B c) as H91.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H91.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (M) H90).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H92.
------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)))) as H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))) as H96.
-------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)) as H98.
--------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H82.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H92.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H92.
------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (C) (B) (D) H83).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H93.
------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))))) as H95.
-------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))) as H97.
--------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))) as H99.
---------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)) as H101.
----------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H93.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M c) as H93.
------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (M) (c)).
-------------------------------------------------------------------------------intro H93.
apply (@euclidean__tactics.Col__nCol__False (B) (M) (c) (H93)).
--------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (M) (c) (H90) (H91) H92).


------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B D M L) as H94.
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H94.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H96.
--------------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H98.
---------------------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H100.
----------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H101.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L M A) as H95.
-------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H16.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M L A) as H96.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H96.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (L) (M) (A) H95).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H97.
----------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L)))) as H99.
------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------ destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))) as H101.
------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L)) as H103.
-------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
exact H97.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L A) as H97.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H97.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (L) (M) (A) H16).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H98.
------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A)) as H100.
------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H101.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A L) as H98.
----------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (L) (A) H97).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D A L) as H99.
------------------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (B) (D) (A) (M) (L) (H94) (H96) H98).
------------------------------------------------------------------------------------ assert (* Cut *) (B = B) as H100.
------------------------------------------------------------------------------------- exact H59.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D B L A) as H101.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D B A L) /\ ((euclidean__defs.Par B D L A) /\ (euclidean__defs.Par D B L A))) as H101.
--------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (D) (A) (L) H99).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D B A L) /\ ((euclidean__defs.Par B D L A) /\ (euclidean__defs.Par D B L A))) as H102.
---------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__defs.Par B D L A) /\ (euclidean__defs.Par D B L A)) as H104.
----------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H105.
-------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet D B L A)) as H102.
--------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B U) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H102.
---------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B U) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
----------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B U) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H103.
------------------------------------------------------------------------------------------ exact __TmpHyp.
------------------------------------------------------------------------------------------ destruct H103 as [x H103].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H104.
------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------- destruct H104 as [x0 H104].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H105.
-------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------- destruct H105 as [x1 H105].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H106.
--------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------- destruct H106 as [x2 H106].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H107.
---------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------- destruct H107 as [x3 H107].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H108.
----------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H110.
------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col D B x) /\ ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H112.
------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col D B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H114.
-------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H116.
--------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col L A x1) /\ ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H118.
---------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col L A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H120.
----------------------------------------------------------------------------------------------------- exact H119.
----------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H122.
------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H124.
------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H126.
-------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H128.
--------------------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
---------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H129.
----------------------------------------------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------------------------------------------- destruct H129 as [x4 H129].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H130.
------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------ destruct H130 as [x5 H130].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H131.
------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------- destruct H131 as [x6 H131].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H132.
-------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------- destruct H132 as [x7 H132].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H133.
--------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------- destruct H133 as [x8 H133].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H134.
---------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H136.
----------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H138.
------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H140.
------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H142.
-------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col A L x6) /\ ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H144.
--------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Col A L x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H146.
---------------------------------------------------------------------------------------------------------------------- exact H145.
---------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H148.
----------------------------------------------------------------------------------------------------------------------- exact H147.
----------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H150.
------------------------------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------------------------------ destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H152.
------------------------------------------------------------------------------------------------------------------------- exact H151.
------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H154.
-------------------------------------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
--------------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H155.
---------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
---------------------------------------------------------------------------------------------------------------------------- destruct H155 as [x9 H155].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H156.
----------------------------------------------------------------------------------------------------------------------------- exact H155.
----------------------------------------------------------------------------------------------------------------------------- destruct H156 as [x10 H156].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H157.
------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [x11 H157].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H158.
------------------------------------------------------------------------------------------------------------------------------- exact H157.
------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [x12 H158].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H159.
-------------------------------------------------------------------------------------------------------------------------------- exact H158.
-------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [x13 H159].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H160.
--------------------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H162.
---------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col B D x9) /\ ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H164.
----------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col B D x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H166.
------------------------------------------------------------------------------------------------------------------------------------ exact H165.
------------------------------------------------------------------------------------------------------------------------------------ destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------------- exact H167.
------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.Col M L x11) /\ ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H170.
-------------------------------------------------------------------------------------------------------------------------------------- exact H169.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.Col M L x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H172.
--------------------------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H174.
---------------------------------------------------------------------------------------------------------------------------------------- exact H173.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H176.
----------------------------------------------------------------------------------------------------------------------------------------- exact H175.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H178.
------------------------------------------------------------------------------------------------------------------------------------------ exact H177.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H178 as [H178 H179].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H181.
--------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [x14 H181].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H182.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [x15 H182].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H183.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [x16 H183].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H184 as [x17 H184].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [x18 H185].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H186.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.Col C E x14) /\ ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.Col C E x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H192.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.Col D B x16) /\ ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.Col D B x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H198.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H207.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [x19 H207].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H208.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [x20 H208].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [x21 H209].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [x22 H210].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H211 as [x23 H211].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.Col C E x19) /\ ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.Col C E x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.Col B D x21) /\ ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.Col B D x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H228.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H230.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H232.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [x24 H233].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H234.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [x25 H234].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H235.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [x26 H235].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [x27 H236].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H237.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H237 as [x28 H237].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H238 as [H238 H239].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H240 as [H240 H241].
assert (* AndElim *) ((euclidean__axioms.Col B D x24) /\ ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H242.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((euclidean__axioms.Col B D x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H244.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H246.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((euclidean__axioms.Col C E x26) /\ ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H248.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((euclidean__axioms.Col C E x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H250.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H250 as [H250 H251].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H254.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H254 H255].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H256.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H255.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H258.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H259.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H259 as [x29 H259].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [x30 H260].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H261.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H261 as [x31 H261].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H262.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [x32 H262].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [x33 H263].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H264.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [H264 H265].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H265.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H266 as [H266 H267].
assert (* AndElim *) ((euclidean__axioms.Col F B x29) /\ ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H268.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((euclidean__axioms.Col F B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H270.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H269.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H272.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((euclidean__axioms.Col G C x31) /\ ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H274.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H273.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((euclidean__axioms.Col G C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H276.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H275.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H276 as [H276 H277].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H277.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H280.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H279.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H282.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H281.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [H282 H283].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H284.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H284.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H285.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [x34 H285].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x34 V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H286.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H285.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H286 as [x35 H286].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X x35)))))))))))) as H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H286.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [x36 H287].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq x36 v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H288.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H287.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H288 as [x37 H288].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 X x37) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H289.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H288.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [x38 H289].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))))) as H290.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H289.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))))) as H292.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H291.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((euclidean__axioms.Col F B x34) /\ ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))) as H294.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H293.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H294 as [H294 H295].
assert (* AndElim *) ((euclidean__axioms.Col F B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))) as H296.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H295.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))) as H298.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H297.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((euclidean__axioms.Col C G x36) /\ ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))) as H300.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H299.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H300 as [H300 H301].
assert (* AndElim *) ((euclidean__axioms.Col C G x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))) as H302.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H301.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
assert (* AndElim *) ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))) as H304.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H303.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H304 as [H304 H305].
assert (* AndElim *) ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))) as H306.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H306 as [H306 H307].
assert (* AndElim *) ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)) as H308.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H307.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H308 as [H308 H309].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H310.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H51.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H310.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H311.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp7.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H311 as [x39 H311].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq x39 V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H312.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H311.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H312 as [x40 H312].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X x40)))))))))))) as H313.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H312.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H313 as [x41 H313].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq x41 v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H314.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H313.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H314 as [x42 H314].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 X x42) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H315.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H314.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H315 as [x43 H315].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))))) as H316.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H315.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H316 as [H316 H317].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))))) as H318.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H317.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H318 as [H318 H319].
assert (* AndElim *) ((euclidean__axioms.Col F B x39) /\ ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))) as H320.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H319.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H320 as [H320 H321].
assert (* AndElim *) ((euclidean__axioms.Col F B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))) as H322.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H321.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H322 as [H322 H323].
assert (* AndElim *) ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))) as H324.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H323.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H324 as [H324 H325].
assert (* AndElim *) ((euclidean__axioms.Col A G x41) /\ ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))) as H326.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H325.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H326 as [H326 H327].
assert (* AndElim *) ((euclidean__axioms.Col A G x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))) as H328.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H327.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H328 as [H328 H329].
assert (* AndElim *) ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))) as H330.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H329.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H330 as [H330 H331].
assert (* AndElim *) ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))) as H332.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H331.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H332 as [H332 H333].
assert (* AndElim *) ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)) as H334.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H333.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H334 as [H334 H335].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H336.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H46.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H336.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H337.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp8.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H337 as [x44 H337].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x44 V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H338.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H337.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H338 as [x45 H338].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X x45)))))))))))) as H339.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H338.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H339 as [x46 H339].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq x46 v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H340.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H339.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H340 as [x47 H340].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 X x47) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H341.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H340.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H341 as [x48 H341].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))))) as H342.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H341.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H342 as [H342 H343].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))))) as H344.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H343.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H344 as [H344 H345].
assert (* AndElim *) ((euclidean__axioms.Col A G x44) /\ ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))) as H346.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H345.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H346 as [H346 H347].
assert (* AndElim *) ((euclidean__axioms.Col A G x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))) as H348.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H347.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H348 as [H348 H349].
assert (* AndElim *) ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))) as H350.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H349.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H350 as [H350 H351].
assert (* AndElim *) ((euclidean__axioms.Col F B x46) /\ ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))) as H352.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H351.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H352 as [H352 H353].
assert (* AndElim *) ((euclidean__axioms.Col F B x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))) as H354.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H353.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H354 as [H354 H355].
assert (* AndElim *) ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))) as H356.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H355.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H356 as [H356 H357].
assert (* AndElim *) ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))) as H358.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H357.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H358 as [H358 H359].
assert (* AndElim *) ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)) as H360.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H359.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H360 as [H360 H361].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H362.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H362.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H363.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp9.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H363 as [x49 H363].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x49 V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H364.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H363.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H364 as [x50 H364].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS u X x50)))))))))))) as H365.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H364.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H365 as [x51 H365].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq x51 v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS x51 X x50)))))))))))) as H366.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H365.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H366 as [x52 H366].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 X x52) /\ (euclidean__axioms.BetS x51 X x50)))))))))))) as H367.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H366.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H367 as [x53 H367].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))))))) as H368.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H367.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H368 as [H368 H369].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))))))) as H370.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H369.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H370 as [H370 H371].
assert (* AndElim *) ((euclidean__axioms.Col A G x49) /\ ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))))) as H372.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H371.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H372 as [H372 H373].
assert (* AndElim *) ((euclidean__axioms.Col A G x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))))) as H374.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H373.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H374 as [H374 H375].
assert (* AndElim *) ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))) as H376.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H375.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H376 as [H376 H377].
assert (* AndElim *) ((euclidean__axioms.Col B F x51) /\ ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))) as H378.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H377.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H378 as [H378 H379].
assert (* AndElim *) ((euclidean__axioms.Col B F x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))) as H380.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H379.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H380 as [H380 H381].
assert (* AndElim *) ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))) as H382.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H381.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H382 as [H382 H383].
assert (* AndElim *) ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))) as H384.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H383.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H384 as [H384 H385].
assert (* AndElim *) ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)) as H386.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H385.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H386 as [H386 H387].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H388.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H388.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H389.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp10.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H389 as [x54 H389].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x54 V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H390.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H389.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H390 as [x55 H390].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS u X x55)))))))))))) as H391.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H390.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H391 as [x56 H391].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq x56 v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS x56 X x55)))))))))))) as H392.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H391.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H392 as [x57 H392].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 X x57) /\ (euclidean__axioms.BetS x56 X x55)))))))))))) as H393.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H392.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H393 as [x58 H393].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))))))) as H394.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H393.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H394 as [H394 H395].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))))))) as H396.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H395.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H396 as [H396 H397].
assert (* AndElim *) ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))))) as H398.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H397.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H398 as [H398 H399].
assert (* AndElim *) ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))))) as H400.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H399.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H400 as [H400 H401].
assert (* AndElim *) ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))) as H402.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H401.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H402 as [H402 H403].
assert (* AndElim *) ((euclidean__axioms.Col G F x56) /\ ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))) as H404.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H403.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H404 as [H404 H405].
assert (* AndElim *) ((euclidean__axioms.Col G F x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))) as H406.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H405.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H406 as [H406 H407].
assert (* AndElim *) ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))) as H408.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H407.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H408 as [H408 H409].
assert (* AndElim *) ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))) as H410.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H409.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H410 as [H410 H411].
assert (* AndElim *) ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)) as H412.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H411.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H412 as [H412 H413].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H414.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H31.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H414.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H415.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp11.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H415 as [x59 H415].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x59 V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H416.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H415.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H416 as [x60 H416].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS u X x60)))))))))))) as H417.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H416.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H417 as [x61 H417].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq x61 v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS x61 X x60)))))))))))) as H418.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H417.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H418 as [x62 H418].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 X x62) /\ (euclidean__axioms.BetS x61 X x60)))))))))))) as H419.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H418.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H419 as [x63 H419].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))))))) as H420.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H419.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H420 as [H420 H421].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))))))) as H422.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H421.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H422 as [H422 H423].
assert (* AndElim *) ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))))) as H424.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H423.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H424 as [H424 H425].
assert (* AndElim *) ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))))) as H426.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H425.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H426 as [H426 H427].
assert (* AndElim *) ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))) as H428.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H427.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H428 as [H428 H429].
assert (* AndElim *) ((euclidean__axioms.Col F G x61) /\ ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))) as H430.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H429.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H430 as [H430 H431].
assert (* AndElim *) ((euclidean__axioms.Col F G x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))) as H432.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H431.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H432 as [H432 H433].
assert (* AndElim *) ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))) as H434.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H433.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H434 as [H434 H435].
assert (* AndElim *) ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))) as H436.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H435.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H436 as [H436 H437].
assert (* AndElim *) ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)) as H438.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H437.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H438 as [H438 H439].
exact H124.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B D L) as H103.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A L) /\ ((euclidean__axioms.nCol D A L) /\ (euclidean__axioms.nCol B D L)))) as H103.
----------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (L) H99).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A L) /\ ((euclidean__axioms.nCol D A L) /\ (euclidean__axioms.nCol B D L)))) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.nCol B A L) /\ ((euclidean__axioms.nCol D A L) /\ (euclidean__axioms.nCol B D L))) as H106.
------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.nCol D A L) /\ (euclidean__axioms.nCol B D L)) as H108.
-------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
exact H109.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H104.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B)))))) as H104.
------------------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (B) (D) (L) H103).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B)))))) as H105.
------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B))))) as H107.
-------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B)))) as H109.
--------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B))) as H111.
---------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B)) as H113.
----------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
exact H111.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H105.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H105.
------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (L) (M) (A) H16).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H106.
-------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A)) as H108.
--------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
exact H106.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq L M) as H106.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H106.
-------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (L) (M) (A) H16).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H107.
--------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A)) as H109.
---------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
exact H109.
------------------------------------------------------------------------------------------- assert (* Cut *) (D = D) as H107.
-------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) D).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B B) as H108.
--------------------------------------------------------------------------------------------- right.
right.
left.
exact H100.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B c M) as H109.
---------------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (D) (B) (L) (A) (B) (M) (c) (H108) (H95) (H104) (H97) (H104) (H105) (H102) (H80) H93).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B c C) as H110.
----------------------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (B) (c) (M) (C) (H109) H10).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B A) as H111.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D B L) /\ ((euclidean__axioms.nCol D L A) /\ ((euclidean__axioms.nCol B L A) /\ (euclidean__axioms.nCol D B A)))) as H111.
------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (B) (L) (A) H101).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D B L) /\ ((euclidean__axioms.nCol D L A) /\ ((euclidean__axioms.nCol B L A) /\ (euclidean__axioms.nCol D B A)))) as H112.
-------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.nCol D L A) /\ ((euclidean__axioms.nCol B L A) /\ (euclidean__axioms.nCol D B A))) as H114.
--------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.nCol B L A) /\ (euclidean__axioms.nCol D B A)) as H116.
---------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H117.
------------------------------------------------------------------------------------------------ assert (* Cut *) (~(B = c)) as H112.
------------------------------------------------------------------------------------------------- intro H112.
assert (* Cut *) (euclidean__axioms.Col D B c) as H113.
-------------------------------------------------------------------------------------------------- right.
right.
left.
exact H112.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D c A) as H114.
--------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H80.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c D B) as H115.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B D c) /\ ((euclidean__axioms.Col B c D) /\ ((euclidean__axioms.Col c D B) /\ ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D))))) as H115.
----------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (c) H113).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B D c) /\ ((euclidean__axioms.Col B c D) /\ ((euclidean__axioms.Col c D B) /\ ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D))))) as H116.
------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col B c D) /\ ((euclidean__axioms.Col c D B) /\ ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D)))) as H118.
------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col c D B) /\ ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D))) as H120.
-------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D)) as H122.
--------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
exact H120.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c D A) as H116.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c D A) /\ ((euclidean__axioms.Col c A D) /\ ((euclidean__axioms.Col A D c) /\ ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D))))) as H116.
------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (c) (A) H114).
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col c D A) /\ ((euclidean__axioms.Col c A D) /\ ((euclidean__axioms.Col A D c) /\ ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D))))) as H117.
------------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col c A D) /\ ((euclidean__axioms.Col A D c) /\ ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D)))) as H119.
-------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col A D c) /\ ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D))) as H121.
--------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D)) as H123.
---------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
exact H117.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D c) as H117.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq D c) /\ (euclidean__axioms.neq D A))) as H117.
------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (c) (A) H80).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq D c) /\ (euclidean__axioms.neq D A))) as H118.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq D c) /\ (euclidean__axioms.neq D A)) as H120.
--------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H120.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq c D) as H118.
------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (c) H117).
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H119.
-------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point c (fun B0: euclidean__axioms.Point => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Per B0 A C) -> ((euclidean__defs.SQ A B0 F G) -> ((euclidean__axioms.TS G B0 A C) -> ((euclidean__defs.SQ B0 C E D) -> ((euclidean__axioms.TS D C B0 A) -> ((euclidean__defs.PG B0 M L D) -> ((euclidean__axioms.BetS B0 M C) -> ((euclidean__axioms.Col C B0 N) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.Per G A B0) -> ((euclidean__defs.Per A B0 F) -> ((euclidean__defs.Per F B0 A) -> ((euclidean__defs.Per D B0 C) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.PG A B0 F G) -> ((euclidean__defs.Par A B0 F G) -> ((euclidean__defs.Par A B0 G F) -> ((euclidean__defs.TP A B0 G F) -> ((euclidean__defs.OS G F A B0) -> ((euclidean__defs.OS F G A B0) -> ((euclidean__axioms.TS G A B0 C) -> ((euclidean__axioms.TS F A B0 C) -> ((euclidean__axioms.Col A B0 a) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.Col B0 A a) -> ((euclidean__defs.Par A G B0 F) -> ((euclidean__defs.Par A G F B0) -> ((euclidean__defs.Par F B0 A G) -> ((euclidean__defs.Par F B0 C G) -> ((euclidean__defs.Par F B0 G C) -> ((~(euclidean__defs.Meet F B0 G C)) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.neq F B0) -> ((B0 = B0) -> ((euclidean__axioms.Col F B0 B0) -> ((euclidean__axioms.BetS B0 a A) -> ((euclidean__axioms.neq B0 a) -> ((euclidean__defs.Out B0 a A) -> ((euclidean__axioms.neq B0 F) -> ((euclidean__defs.Out B0 F F) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.nCol F B0 A) -> ((euclidean__defs.CongA F B0 A F B0 A) -> ((euclidean__defs.Out B0 A a) -> ((euclidean__defs.CongA F B0 A F B0 a) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__defs.Out B0 C C) -> ((euclidean__defs.CongA A B0 C A B0 C) -> ((euclidean__defs.CongA A B0 C a B0 C) -> ((euclidean__defs.SumA F B0 A A B0 C F B0 C) -> ((euclidean__axioms.Col C B0 c) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.PG B0 C E D) -> ((euclidean__defs.Par B0 D C E) -> ((euclidean__defs.Par C E B0 D) -> ((euclidean__defs.Par C E D B0) -> ((euclidean__axioms.Col B0 C c) -> ((euclidean__axioms.Col B0 M C) -> ((euclidean__axioms.Col C B0 M) -> ((euclidean__axioms.Col C B0 c) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Col B0 M c) -> ((euclidean__defs.Par B0 D M L) -> ((euclidean__defs.Par B0 D A L) -> ((B0 = B0) -> ((euclidean__defs.Par D B0 L A) -> ((~(euclidean__defs.Meet D B0 L A)) -> ((euclidean__axioms.nCol B0 D L) -> ((euclidean__axioms.neq D B0) -> ((euclidean__axioms.Col D B0 B0) -> ((euclidean__axioms.BetS B0 c M) -> ((euclidean__axioms.BetS B0 c C) -> ((euclidean__axioms.nCol D B0 A) -> ((euclidean__axioms.Col D B0 c) -> ((euclidean__axioms.Col c D B0) -> (euclidean__axioms.Col D B0 A)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := B).
---------------------------------------------------------------------------------------------------------intro H119.
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
exact H114.

--------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------------------------------------- exact H3.
--------------------------------------------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------------------------------------------- exact H8.
--------------------------------------------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------------------------------------------- exact H22.
--------------------------------------------------------------------------------------------------------- exact H23.
--------------------------------------------------------------------------------------------------------- exact H24.
--------------------------------------------------------------------------------------------------------- exact H26.
--------------------------------------------------------------------------------------------------------- exact H27.
--------------------------------------------------------------------------------------------------------- exact H28.
--------------------------------------------------------------------------------------------------------- exact H29.
--------------------------------------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------------------------------------- exact H31.
--------------------------------------------------------------------------------------------------------- exact H32.
--------------------------------------------------------------------------------------------------------- exact H33.
--------------------------------------------------------------------------------------------------------- exact H34.
--------------------------------------------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------------------------------------------- exact H36.
--------------------------------------------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------------------------------------------- exact H44.
--------------------------------------------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------------------------------------------- exact H46.
--------------------------------------------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------------------------- exact H56.
--------------------------------------------------------------------------------------------------------- exact H58.
--------------------------------------------------------------------------------------------------------- exact H59.
--------------------------------------------------------------------------------------------------------- exact H60.
--------------------------------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------------------------------- exact H62.
--------------------------------------------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------------------------------------- exact H74.
--------------------------------------------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (D) (B) (A) (H111) H119).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B c C) as H113.
-------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (c) (C)).
---------------------------------------------------------------------------------------------------right.
right.
exact H110.

--------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C c) as H114.
--------------------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (c) (C) H113).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H115.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H115.
----------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H29).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H116.
------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------ destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H118.
------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H120.
-------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H122.
--------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
exact H123.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A C B A) as H116.
----------------------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (C) (B) (A) H115).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (A = A) as H117.
------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B A) as H118.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)))))) as H118.
-------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (B) (A) H115).
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)))))) as H119.
--------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))))) as H121.
---------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)))) as H123.
----------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H125.
------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H127.
------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H121.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H119.
-------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
---------------------------------------------------------------------------------------------------------right.
left.
exact H117.

--------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A c B A) as H120.
--------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (C) (B) (A) (C) (B) (A) (c) (A) (H116) (H114) H119).
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C D B) as H121.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol E D B) /\ (euclidean__axioms.nCol C E B)))) as H121.
----------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (C) (E) (D) (B) H87).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol E D B) /\ (euclidean__axioms.nCol C E B)))) as H122.
------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol E D B) /\ (euclidean__axioms.nCol C E B))) as H124.
------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.nCol E D B) /\ (euclidean__axioms.nCol C E B)) as H126.
-------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
exact H124.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B C) as H122.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C))))) as H122.
------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (C) (D) (B) H121).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C))))) as H123.
------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C)))) as H125.
-------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C))) as H127.
--------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C)) as H129.
---------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H125.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B C D B C) as H123.
------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (D) (B) (C) H122).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B D) as H124.
------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (B) H104).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D D) as H125.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (D) (D)).
---------------------------------------------------------------------------------------------------------------right.
left.
exact H107.

--------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B C D B c) as H126.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (B) (C) (D) (B) (C) (D) (c) (H123) (H125) H114).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.SumA D B C C B A D B A) as H127.
---------------------------------------------------------------------------------------------------------------- exists c.
split.
----------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------------ exact H80.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A D B C) as H128.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 (F) (B) (A) (D) (B) (C) (H27) H28).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H129.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (C) H29).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F B C D B A) as H130.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__angleaddition.lemma__angleaddition (F) (B) (A) (A) (B) (C) (F) (B) (C) (D) (B) (C) (C) (B) (A) (D) (B) (A) (H77) (H128) (H129) H127).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B A F B C) as H131.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (B) (C) (D) (B) (A) H130).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C B F)) as H132.
--------------------------------------------------------------------------------------------------------------------- intro H132.
assert (* Cut *) (euclidean__axioms.Col F B C) as H133.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C F) /\ ((euclidean__axioms.Col B F C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C))))) as H133.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (F) H132).
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C F) /\ ((euclidean__axioms.Col B F C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C))))) as H134.
------------------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col B F C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C)))) as H136.
------------------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C))) as H138.
-------------------------------------------------------------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C)) as H140.
--------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
exact H141.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per C B A) as H134.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (F) (B) (C) (A) (H27) (H133) H92).
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Per C B A)) as H135.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__8__7.lemma__8__7 (C) (A) (B) H0).
------------------------------------------------------------------------------------------------------------------------ apply (@H135 H134).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B C) as H133.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B F) as H133.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (B) (F) H132).
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C F) /\ ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol F C B) /\ ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C))))) as H134.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (C) (B) (F) H133).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B C F) /\ ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol F C B) /\ ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C))))) as H135.
------------------------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol F C B) /\ ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C)))) as H137.
-------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.nCol F C B) /\ ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C))) as H139.
--------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C)) as H141.
---------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H142.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B C C B F) as H134.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (F) (B) (C) H133).
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B A C B F) as H135.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (D) (B) (A) (F) (B) (C) (C) (B) (F) (H131) H134).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A B B F) as H136.
------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H136.
-------------------------------------------------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H138.
--------------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H140.
---------------------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H142.
----------------------------------------------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H144.
------------------------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H146.
------------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H150.
--------------------------------------------------------------------------------------------------------------------------------- exact H149.
--------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------- exact H151.
---------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H154.
----------------------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H156.
------------------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H158.
------------------------------------------------------------------------------------------------------------------------------------- exact H157.
------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
exact H150.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B F B) as H137.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A F B) /\ ((euclidean__axioms.Cong B A B F) /\ (euclidean__axioms.Cong A B F B))) as H137.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (B) (F) H136).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A F B) /\ ((euclidean__axioms.Cong B A B F) /\ (euclidean__axioms.Cong A B F B))) as H138.
---------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Cong B A B F) /\ (euclidean__axioms.Cong A B F B)) as H140.
----------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
exact H141.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B A B) as H138.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (A) (B) (B) H137).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F B A) as H139.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B F B A) /\ ((euclidean__axioms.Cong B F A B) /\ (euclidean__axioms.Cong F B B A))) as H139.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (B) (A) (B) H138).
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B F B A) /\ ((euclidean__axioms.Cong B F A B) /\ (euclidean__axioms.Cong F B B A))) as H140.
------------------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Cong B F A B) /\ (euclidean__axioms.Cong F B B A)) as H142.
------------------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
exact H140.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B F) as H140.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (F) (A) H139).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C D B) as H141.
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H141.
------------------------------------------------------------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H143.
-------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H145.
--------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H147.
---------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H149.
----------------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H151.
------------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H153.
------------------------------------------------------------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H155.
-------------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H157.
--------------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H159.
---------------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H161.
----------------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H163.
------------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H163 as [H163 H164].
exact H145.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D B B C) as H142.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (B) (C) (B) H141).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D B C) as H143.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D C B) /\ ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong D B C B))) as H143.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (B) (C) H142).
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D C B) /\ ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong D B C B))) as H144.
---------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong D B C B)) as H146.
----------------------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
exact H146.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H144.
--------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__04.proposition__04 (B) (D) (A) (B) (C) (F) (H143) (H140) H135).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D F C) as H145.
---------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H145.
----------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H147.
------------------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------------------ destruct H147 as [H147 H148].
assert (* Cut *) ((euclidean__axioms.Cong A D F C) /\ ((euclidean__axioms.Cong A D C F) /\ (euclidean__axioms.Cong D A F C))) as H149.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (A) (C) (F) H145).
------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A D F C) /\ ((euclidean__axioms.Cong A D C F) /\ (euclidean__axioms.Cong D A F C))) as H150.
-------------------------------------------------------------------------------------------------------------------------------------- exact H149.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.Cong A D C F) /\ (euclidean__axioms.Cong D A F C)) as H152.
--------------------------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
exact H150.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B F C B A D) as H146.
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H146.
------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------ destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H148.
------------------------------------------------------------------------------------------------------------------------------------- exact H147.
------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (A) (D) (B) (F) (C) H149).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A D) as H147.
------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H147.
------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H149.
-------------------------------------------------------------------------------------------------------------------------------------- exact H148.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
apply (@euclidean__tactics.nCol__notCol (B) (A) (D)).
---------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (A) (D)).
----------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (B) (F) (C) (B) (A) (D) H146).


------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B D) as H148.
------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H148.
-------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H150.
--------------------------------------------------------------------------------------------------------------------------------------- exact H149.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (A) (D) H147).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B))))) as H153.
----------------------------------------------------------------------------------------------------------------------------------------- exact H152.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B)))) as H155.
------------------------------------------------------------------------------------------------------------------------------------------ exact H154.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B))) as H157.
------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B)) as H159.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
exact H153.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle A B D) as H149.
-------------------------------------------------------------------------------------------------------------------------------------- exact H148.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 A B D F B C) as H150.
--------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------- exact H143.
----------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D F B C) as H151.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H151.
----------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H153.
------------------------------------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H153 as [H153 H154].
apply (@euclidean__axioms.axiom__congruentequal (A) (B) (D) (F) (B) (C) H150).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M L D) as H152.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H152.
------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H154.
------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H156.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H158.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H160.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H162.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
exact H162.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D M L) as H153.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H153.
------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H155.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H157.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__defs.Par A B F G) /\ (euclidean__defs.Par A G B F)) as H159.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H161.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H163.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H8.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H163 as [H163 H164].
exact H94.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par M L B D) as H154.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H154.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H156.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (D) (M) (L) H153).
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B D L) as H155.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H155.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H157.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* Cut *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H159.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (M) (L) (D) H152).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H160.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L)) as H162.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
exact H163.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG M B D L) as H156.
--------------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M L A) as H157.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H157.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H159.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H158.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H159 as [H159 H160].
assert (* Cut *) ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col B B D) /\ ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D))))) as H161.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (B) H108).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col B B D) /\ ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D))))) as H162.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col B B D) /\ ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D)))) as H164.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D))) as H166.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D)) as H168.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
exact H96.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET M B D A B D) as H158.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H158.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H160.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
apply (@proposition__41.proposition__41 (M) (B) (D) (L) (A) (H156) H157).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B F G) as H159.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H159.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H161.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
exact H30.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG B A G F) as H160.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H160.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H162.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
apply (@lemma__PGflip.lemma__PGflip (A) (B) (F) (G) H159).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A C) as H161.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G C) as H162.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H162.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H164.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* Cut *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H166.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (C) H161).
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G)))) as H169.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))) as H171.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G)) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
exact H167.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F C B F) as H163.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H163.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H165.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
apply (@proposition__41.proposition__41 (A) (B) (F) (G) (C) (H159) H162).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F F B C) as H164.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H166.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* Cut *) ((euclidean__axioms.ET A B F B F C) /\ ((euclidean__axioms.ET A B F C F B) /\ ((euclidean__axioms.ET A B F B C F) /\ ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B))))) as H168.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (F) (C) (B) (F) H163).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET A B F B F C) /\ ((euclidean__axioms.ET A B F C F B) /\ ((euclidean__axioms.ET A B F B C F) /\ ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B))))) as H169.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.ET A B F C F B) /\ ((euclidean__axioms.ET A B F B C F) /\ ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B)))) as H171.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.ET A B F B C F) /\ ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B))) as H173.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B)) as H175.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H174.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H175 as [H175 H176].
exact H175.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F B C A B D) as H165.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H165.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H167.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (D) (F) (B) (C) H151).
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A B F A B D) as H166.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H166.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H168.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
apply (@euclidean__axioms.axiom__ETtransitive (A) (B) (F) (A) (B) (D) (F) (B) (C) (H164) H165).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D M B D) as H167.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H167.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H169.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
apply (@euclidean__axioms.axiom__ETsymmetric (M) (B) (D) (A) (B) (D) H158).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F M B D) as H168.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H168.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H170.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
apply (@euclidean__axioms.axiom__ETtransitive (A) (B) (F) (M) (B) (D) (A) (B) (D) (H166) H167).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 A B F F G A) as H169.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H169.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H170.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H171 as [H171 H172].
assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H174.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H173 (A0) (B0) (C0) (D0) __).
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H175.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H174 (A0) (B0) (C0) (D0) __).
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H175 (A0) (B0) (C0) (D0) __).
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H176 (B) (F) (A) (G) H160).
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F F G A) as H170.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H172.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
apply (@euclidean__axioms.axiom__congruentequal (A) (B) (F) (F) (G) (A) H169).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG B M L D) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H173.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
exact H8.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 M B D D L M) as H172.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H177.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@H176 (A0) (B0) (C0) (D0) __).
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H177 (A0) (B0) (C0) (D0) __).
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H178 (A0) (B0) (C0) (D0) __).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H179 (B) (D) (M) (L) H171).
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET M B D D L M) as H173.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H173.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H175.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
apply (@euclidean__axioms.axiom__congruentequal (M) (B) (D) (D) (L) (M) H172).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A A B F) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H174.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H176.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (F) (F) (G) (A) H170).
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A A B D) as H175.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
apply (@euclidean__axioms.axiom__ETtransitive (F) (G) (A) (A) (B) (D) (A) (B) (F) (H174) H166).
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A M B D) as H176.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
apply (@euclidean__axioms.axiom__ETtransitive (F) (G) (A) (M) (B) (D) (A) (B) (D) (H175) H167).
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A D L M) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H179.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
apply (@euclidean__axioms.axiom__ETtransitive (F) (G) (A) (D) (L) (M) (M) (B) (D) (H176) H173).
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F G A D M L) as H178.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H180.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* Cut *) ((euclidean__axioms.ET F G A L M D) /\ ((euclidean__axioms.ET F G A D M L) /\ ((euclidean__axioms.ET F G A L D M) /\ ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L))))) as H182.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (G) (A) (D) (L) (M) H177).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F G A L M D) /\ ((euclidean__axioms.ET F G A D M L) /\ ((euclidean__axioms.ET F G A L D M) /\ ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L))))) as H183.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.ET F G A D M L) /\ ((euclidean__axioms.ET F G A L D M) /\ ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L)))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.ET F G A L D M) /\ ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L))) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L)) as H189.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M L F G A) as H179.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H181.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
apply (@euclidean__axioms.axiom__ETsymmetric (F) (G) (A) (D) (M) (L) H178).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M L F A G) as H180.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H182.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* Cut *) ((euclidean__axioms.ET D M L G A F) /\ ((euclidean__axioms.ET D M L F A G) /\ ((euclidean__axioms.ET D M L G F A) /\ ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G))))) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (D) (M) (L) (F) (G) (A) H179).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET D M L G A F) /\ ((euclidean__axioms.ET D M L F A G) /\ ((euclidean__axioms.ET D M L G F A) /\ ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G))))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.ET D M L F A G) /\ ((euclidean__axioms.ET D M L G F A) /\ ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G)))) as H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.ET D M L G F A) /\ ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G)) as H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
exact H187.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A G D M L) as H181.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H181.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H183 as [H183 H184].
apply (@euclidean__axioms.axiom__ETsymmetric (D) (M) (L) (F) (A) (G) H180).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F D M B) as H182.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* Cut *) ((euclidean__axioms.ET A B F B D M) /\ ((euclidean__axioms.ET A B F M D B) /\ ((euclidean__axioms.ET A B F B M D) /\ ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B))))) as H186.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (F) (M) (B) (D) H168).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET A B F B D M) /\ ((euclidean__axioms.ET A B F M D B) /\ ((euclidean__axioms.ET A B F B M D) /\ ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B))))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.ET A B F M D B) /\ ((euclidean__axioms.ET A B F B M D) /\ ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B)))) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.ET A B F B M D) /\ ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B)) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
exact H194.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M B A B F) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (F) (D) (M) (B) H182).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET D M B F A B) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* Cut *) ((euclidean__axioms.ET D M B B F A) /\ ((euclidean__axioms.ET D M B A F B) /\ ((euclidean__axioms.ET D M B B A F) /\ ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (D) (M) (B) (A) (B) (F) H183).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET D M B B F A) /\ ((euclidean__axioms.ET D M B A F B) /\ ((euclidean__axioms.ET D M B B A F) /\ ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B))))) as H189.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.ET D M B A F B) /\ ((euclidean__axioms.ET D M B B A F) /\ ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B)))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.ET D M B B A F) /\ ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B)) as H195.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
exact H196.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A B D M B) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H185.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H187.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
apply (@euclidean__axioms.axiom__ETsymmetric (D) (M) (B) (F) (A) (B) H184).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__defs.Midpoint A m F) /\ (euclidean__defs.Midpoint B m G)) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H186.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H188.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
apply (@lemma__diagonalsbisect.lemma__diagonalsbisect (A) (B) (F) (G) H159).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__defs.Midpoint A m F) /\ (euclidean__defs.Midpoint B m G))) as H187.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [m H187].
assert (* AndElim *) ((euclidean__defs.Midpoint A m F) /\ (euclidean__defs.Midpoint B m G)) as H188.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H190.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C)) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* Cut *) (euclidean__axioms.BetS A m F) as H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS B m G) /\ (euclidean__axioms.Cong B m m G)) as H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.BetS A m F) /\ (euclidean__axioms.Cong A m m F)) as H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B m G) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS B m G) /\ (euclidean__axioms.Cong B m m G)) as H195.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.BetS A m F) /\ (euclidean__axioms.Cong A m m F)) as H197.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
exact H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F m A) as H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (F) H194).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (n: euclidean__axioms.Point), (euclidean__defs.Midpoint B n L) /\ (euclidean__defs.Midpoint M n D)) as H197.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsbisect.lemma__diagonalsbisect (B) (M) (L) (D) H171).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists n: euclidean__axioms.Point, ((euclidean__defs.Midpoint B n L) /\ (euclidean__defs.Midpoint M n D))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H198 as [n H198].
assert (* AndElim *) ((euclidean__defs.Midpoint B n L) /\ (euclidean__defs.Midpoint M n D)) as H199.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* Cut *) (euclidean__axioms.BetS B n L) as H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS M n D) /\ (euclidean__axioms.Cong M n n D)) as H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.BetS B n L) /\ (euclidean__axioms.Cong B n n L)) as H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.BetS B m G) /\ (euclidean__axioms.Cong B m m G)) as H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.BetS A m F) /\ (euclidean__axioms.Cong A m m F)) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H188.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [H207 H208].
exact H203.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M n D) as H202.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS M n D) /\ (euclidean__axioms.Cong M n n D)) as H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.BetS B n L) /\ (euclidean__axioms.Cong B n n L)) as H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.BetS B m G) /\ (euclidean__axioms.Cong B m m G)) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H189.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.BetS A m F) /\ (euclidean__axioms.Cong A m m F)) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
exact H202.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D n M) as H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (M) (n) (D) H202).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M n D) as H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D M n) as H205.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col n M D) /\ ((euclidean__axioms.Col n D M) /\ ((euclidean__axioms.Col D M n) /\ ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M))))) as H205.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (M) (n) (D) H204).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col n M D) /\ ((euclidean__axioms.Col n D M) /\ ((euclidean__axioms.Col D M n) /\ ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M))))) as H206.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.Col n D M) /\ ((euclidean__axioms.Col D M n) /\ ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M)))) as H208.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.Col D M n) /\ ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M))) as H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M)) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B M D) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B M L) /\ ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol M L D) /\ (euclidean__axioms.nCol B M D)))) as H206.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (M) (L) (D) H152).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B M L) /\ ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol M L D) /\ (euclidean__axioms.nCol B M D)))) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol M L D) /\ (euclidean__axioms.nCol B M D))) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.nCol M L D) /\ (euclidean__axioms.nCol B M D)) as H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D M B) as H207.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol M B D) /\ ((euclidean__axioms.nCol M D B) /\ ((euclidean__axioms.nCol D B M) /\ ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B))))) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (M) (D) H206).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol M B D) /\ ((euclidean__axioms.nCol M D B) /\ ((euclidean__axioms.nCol D B M) /\ ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B))))) as H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.nCol M D B) /\ ((euclidean__axioms.nCol D B M) /\ ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B)))) as H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.nCol D B M) /\ ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B)) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
exact H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F B A G D B M L) as H208.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 (F) (A) (B) (G) (m) (D) (M) (B) (L) (n) (H185) (H181) (H195)).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------left.
exact H196.

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------left.
exact H203.

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F B A G B M L D) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF F B A G B M L D) /\ ((euclidean__axioms.EF F B A G L M B D) /\ ((euclidean__axioms.EF F B A G M L D B) /\ ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B))))))) as H209.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (F) (B) (A) (G) (D) (B) (M) (L) H208).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF F B A G B M L D) /\ ((euclidean__axioms.EF F B A G L M B D) /\ ((euclidean__axioms.EF F B A G M L D B) /\ ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B))))))) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.EF F B A G L M B D) /\ ((euclidean__axioms.EF F B A G M L D B) /\ ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B)))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.EF F B A G M L D B) /\ ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B))))) as H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B)))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B))) as H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B)) as H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
exact H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D F B A G) as H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (F) (B) (A) (G) (B) (M) (L) (D) H209).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D A B F G) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.EF B M L D B A G F) /\ ((euclidean__axioms.EF B M L D G A B F) /\ ((euclidean__axioms.EF B M L D A G F B) /\ ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B))))))) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (B) (M) (L) (D) (F) (B) (A) (G) H210).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF B M L D B A G F) /\ ((euclidean__axioms.EF B M L D G A B F) /\ ((euclidean__axioms.EF B M L D A G F B) /\ ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B))))))) as H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.EF B M L D G A B F) /\ ((euclidean__axioms.EF B M L D A G F B) /\ ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B)))))) as H214.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.EF B M L D A G F B) /\ ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B))))) as H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B)))) as H218.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B))) as H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B)) as H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A B F G B M L D) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (B) (M) (L) (D) (A) (B) (F) (G) H211).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exists M.
exists L.
split.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H14.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H16.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H17.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
Qed.
