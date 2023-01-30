Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__PGrotate.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__diagonalsmeet.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__34.
Require Export proposition__35.
Definition proposition__37 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A D B C) -> (euclidean__axioms.ET A B C D B C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__defs.Par B C A D) as H0.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H).
- assert (* Cut *) (euclidean__defs.Par C B A D) as H1.
-- assert (* Cut *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H1.
--- apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (A) (D) H0).
--- assert (* AndElim *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H2.
---- exact H1.
---- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A)) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
exact H2.
-- assert (* Cut *) (A = A) as H2.
--- apply (@logic.eq__refl (Point) A).
--- assert (* Cut *) (D = D) as H3.
---- apply (@logic.eq__refl (Point) D).
---- assert (* Cut *) (euclidean__axioms.Col A D A) as H4.
----- right.
left.
exact H2.
----- assert (* Cut *) (euclidean__axioms.Col A D D) as H5.
------ right.
right.
left.
exact H3.
------ assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__defs.PG A E B C) /\ (euclidean__axioms.Col A D E)) as H6.
------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (A) (B) (C) (A) (D) (H1) H4).
------- assert (exists E: euclidean__axioms.Point, ((euclidean__defs.PG A E B C) /\ (euclidean__axioms.Col A D E))) as H7.
-------- exact H6.
-------- destruct H7 as [E H7].
assert (* AndElim *) ((euclidean__defs.PG A E B C) /\ (euclidean__axioms.Col A D E)) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__defs.PG D F B C) /\ (euclidean__axioms.Col A D F)) as H10.
---------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (D) (B) (C) (A) (D) (H1) H5).
---------- assert (exists F: euclidean__axioms.Point, ((euclidean__defs.PG D F B C) /\ (euclidean__axioms.Col A D F))) as H11.
----------- exact H10.
----------- destruct H11 as [F H11].
assert (* AndElim *) ((euclidean__defs.PG D F B C) /\ (euclidean__axioms.Col A D F)) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* Cut *) (euclidean__defs.PG E B C A) as H14.
------------- apply (@lemma__PGrotate.lemma__PGrotate (A) (E) (B) (C) H8).
------------- assert (* Cut *) (euclidean__defs.PG F B C D) as H15.
-------------- apply (@lemma__PGrotate.lemma__PGrotate (D) (F) (B) (C) H12).
-------------- assert (* Cut *) (euclidean__axioms.Col D A F) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H16.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (F) H13).
---------------- assert (* AndElim *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A)) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
exact H17.
--------------- assert (* Cut *) (euclidean__axioms.Col D A E) as H17.
---------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H17.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H9).
----------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
exact H18.
---------------- assert (* Cut *) (euclidean__axioms.nCol C A D) as H18.
----------------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol C B D)))) as H18.
------------------ apply (@lemma__parallelNC.lemma__parallelNC (C) (B) (A) (D) H1).
------------------ assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol C B D)))) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol C B D))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol C B D)) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
exact H21.
----------------- assert (* Cut *) (euclidean__axioms.neq A D) as H19.
------------------ assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C)))))) as H19.
------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (A) (D) H18).
------------------- assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C)))))) as H20.
-------------------- exact H19.
-------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C))))) as H22.
--------------------- exact H21.
--------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C)))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D C)) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
exact H22.
------------------ assert (* Cut *) (euclidean__axioms.neq D A) as H20.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (D) H19).
------------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H21.
-------------------- apply (@euclidean__tactics.not__nCol__Col (A) (F) (E)).
---------------------intro H21.
apply (@euclidean__tactics.Col__nCol__False (A) (F) (E) (H21)).
----------------------apply (@lemma__collinear4.lemma__collinear4 (D) (A) (F) (E) (H16) (H17) H20).


-------------------- assert (* Cut *) (euclidean__axioms.Col E A D) as H22.
--------------------- assert (* Cut *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D))))) as H22.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (E) H17).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D))))) as H23.
----------------------- exact H22.
----------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D)))) as H25.
------------------------ exact H24.
------------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D)) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
exact H30.
--------------------- assert (* Cut *) (euclidean__axioms.Col E A F) as H23.
---------------------- assert (* Cut *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H23.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (E) H21).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A)))) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A)) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
exact H28.
---------------------- assert (* Cut *) (euclidean__axioms.EF E B C A F B C D) as H24.
----------------------- apply (@proposition__35.proposition__35 (E) (B) (C) (A) (F) (D) (H14) (H15) (H23) H22).
----------------------- assert (* Cut *) (euclidean__axioms.Cong__3 B E A A C B) as H25.
------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H25.
------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
-------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
-------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H26.
-------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
--------------------------- apply (@H25 (A0) (B0) (C0) (D0) __).
--------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H27.
--------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
---------------------------- apply (@H26 (A0) (B0) (C0) (D0) __).
---------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H28.
---------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
----------------------------- apply (@H27 (A0) (B0) (C0) (D0) __).
----------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------- apply (@H28 (E) (A) (B) (C) H14).
------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 B F D D C B) as H26.
------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H26.
-------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
--------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
--------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H27.
--------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
---------------------------- apply (@H26 (A0) (B0) (C0) (D0) __).
---------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H28.
---------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
----------------------------- apply (@H27 (A0) (B0) (C0) (D0) __).
----------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H29.
----------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
------------------------------ apply (@H28 (A0) (B0) (C0) (D0) __).
------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------- apply (@H29 (F) (D) (B) (C) H15).
------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M A)) as H27.
-------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (E) (B) (C) (A) H14).
-------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M A))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [M H28].
assert (* AndElim *) ((euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M A)) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS F m C) /\ (euclidean__axioms.BetS B m D)) as H31.
----------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (F) (B) (C) (D) H15).
----------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS F m C) /\ (euclidean__axioms.BetS B m D))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [m H32].
assert (* AndElim *) ((euclidean__axioms.BetS F m C) /\ (euclidean__axioms.BetS B m D)) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__axioms.Col B M A) as H35.
-------------------------------- right.
right.
right.
right.
left.
exact H30.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B m D) as H36.
--------------------------------- right.
right.
right.
right.
left.
exact H34.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A M) as H37.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H37.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (A) H35).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B)))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B)) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
exact H44.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B D m) as H38.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col m B D) /\ ((euclidean__axioms.Col m D B) /\ ((euclidean__axioms.Col D B m) /\ ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B))))) as H38.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (m) (D) H36).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col m B D) /\ ((euclidean__axioms.Col m D B) /\ ((euclidean__axioms.Col D B m) /\ ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B))))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col m D B) /\ ((euclidean__axioms.Col D B m) /\ ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B)))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col D B m) /\ ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B))) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B)) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
exact H45.
----------------------------------- assert (* Cut *) (euclidean__defs.Par E B C A) as H39.
------------------------------------ assert (* AndElim *) ((euclidean__defs.Par F B C D) /\ (euclidean__defs.Par F D B C)) as H39.
------------------------------------- exact H15.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.Par E B C A) /\ (euclidean__defs.Par E A B C)) as H41.
-------------------------------------- exact H14.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.Par D F B C) /\ (euclidean__defs.Par D C F B)) as H43.
--------------------------------------- exact H12.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par A C E B)) as H45.
---------------------------------------- exact H8.
---------------------------------------- destruct H45 as [H45 H46].
exact H41.
------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E B A) as H40.
------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol E B A)))) as H40.
-------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (E) (B) (C) (A) H39).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol E B A)))) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol E B A))) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ (euclidean__axioms.nCol E B A)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
exact H46.
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A E) as H41.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol E A B) /\ (euclidean__axioms.nCol A B E))))) as H41.
--------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (B) (A) H40).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B E A) /\ ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol E A B) /\ (euclidean__axioms.nCol A B E))))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol E A B) /\ (euclidean__axioms.nCol A B E)))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.nCol A E B) /\ ((euclidean__axioms.nCol E A B) /\ (euclidean__axioms.nCol A B E))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ (euclidean__axioms.nCol A B E)) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
exact H44.
-------------------------------------- assert (* Cut *) (euclidean__axioms.TS E B A C) as H42.
--------------------------------------- exists M.
split.
---------------------------------------- exact H29.
---------------------------------------- split.
----------------------------------------- exact H37.
----------------------------------------- exact H41.
--------------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A E) as H43.
---------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (B) (A) (E) (C) H42).
---------------------------------------- assert (* Cut *) (euclidean__defs.Par D F B C) as H44.
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par F B C D) /\ (euclidean__defs.Par F D B C)) as H44.
------------------------------------------ exact H15.
------------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Par E B C A) /\ (euclidean__defs.Par E A B C)) as H46.
------------------------------------------- exact H14.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Par D F B C) /\ (euclidean__defs.Par D C F B)) as H48.
-------------------------------------------- exact H12.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par A C E B)) as H50.
--------------------------------------------- exact H8.
--------------------------------------------- destruct H50 as [H50 H51].
exact H48.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D F B) as H45.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D F B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol D F C)))) as H45.
------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (F) (B) (C) H44).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D F B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol D F C)))) as H46.
-------------------------------------------- exact H45.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol D F C))) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol D F C)) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
exact H46.
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B D F) as H46.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F D B) /\ ((euclidean__axioms.nCol F B D) /\ ((euclidean__axioms.nCol B D F) /\ ((euclidean__axioms.nCol D B F) /\ (euclidean__axioms.nCol B F D))))) as H46.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (F) (B) H45).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F D B) /\ ((euclidean__axioms.nCol F B D) /\ ((euclidean__axioms.nCol B D F) /\ ((euclidean__axioms.nCol D B F) /\ (euclidean__axioms.nCol B F D))))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol F B D) /\ ((euclidean__axioms.nCol B D F) /\ ((euclidean__axioms.nCol D B F) /\ (euclidean__axioms.nCol B F D)))) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol B D F) /\ ((euclidean__axioms.nCol D B F) /\ (euclidean__axioms.nCol B F D))) as H51.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D B F) /\ (euclidean__axioms.nCol B F D)) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
exact H51.
------------------------------------------- assert (* Cut *) (euclidean__axioms.TS F B D C) as H47.
-------------------------------------------- exists m.
split.
--------------------------------------------- exact H33.
--------------------------------------------- split.
---------------------------------------------- exact H38.
---------------------------------------------- exact H46.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C B D F) as H48.
--------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (B) (D) (F) (C) H47).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E A A C B) as H49.
---------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (B) (E) (A) (A) (C) (B) H25).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B E A C B A) as H50.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B E A C B A) /\ ((euclidean__axioms.ET B E A A B C) /\ ((euclidean__axioms.ET B E A C A B) /\ ((euclidean__axioms.ET B E A B C A) /\ (euclidean__axioms.ET B E A B A C))))) as H50.
------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (B) (E) (A) (A) (C) (B) H49).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET B E A C B A) /\ ((euclidean__axioms.ET B E A A B C) /\ ((euclidean__axioms.ET B E A C A B) /\ ((euclidean__axioms.ET B E A B C A) /\ (euclidean__axioms.ET B E A B A C))))) as H51.
------------------------------------------------- exact H50.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.ET B E A A B C) /\ ((euclidean__axioms.ET B E A C A B) /\ ((euclidean__axioms.ET B E A B C A) /\ (euclidean__axioms.ET B E A B A C)))) as H53.
-------------------------------------------------- exact H52.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.ET B E A C A B) /\ ((euclidean__axioms.ET B E A B C A) /\ (euclidean__axioms.ET B E A B A C))) as H55.
--------------------------------------------------- exact H54.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.ET B E A B C A) /\ (euclidean__axioms.ET B E A B A C)) as H57.
---------------------------------------------------- exact H56.
---------------------------------------------------- destruct H57 as [H57 H58].
exact H51.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A B E A) as H51.
------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (B) (E) (A) (C) (B) (A) H50).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET C B A B A E) as H52.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET C B A E A B) /\ ((euclidean__axioms.ET C B A B A E) /\ ((euclidean__axioms.ET C B A E B A) /\ ((euclidean__axioms.ET C B A A E B) /\ (euclidean__axioms.ET C B A A B E))))) as H52.
-------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (C) (B) (A) (B) (E) (A) H51).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET C B A E A B) /\ ((euclidean__axioms.ET C B A B A E) /\ ((euclidean__axioms.ET C B A E B A) /\ ((euclidean__axioms.ET C B A A E B) /\ (euclidean__axioms.ET C B A A B E))))) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.ET C B A B A E) /\ ((euclidean__axioms.ET C B A E B A) /\ ((euclidean__axioms.ET C B A A E B) /\ (euclidean__axioms.ET C B A A B E)))) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.ET C B A E B A) /\ ((euclidean__axioms.ET C B A A E B) /\ (euclidean__axioms.ET C B A A B E))) as H57.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.ET C B A A E B) /\ (euclidean__axioms.ET C B A A B E)) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [H59 H60].
exact H55.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B F D D C B) as H53.
-------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (B) (F) (D) (D) (C) (B) H26).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B F D C B D) as H54.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B F D C B D) /\ ((euclidean__axioms.ET B F D D B C) /\ ((euclidean__axioms.ET B F D C D B) /\ ((euclidean__axioms.ET B F D B C D) /\ (euclidean__axioms.ET B F D B D C))))) as H54.
---------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (B) (F) (D) (D) (C) (B) H53).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET B F D C B D) /\ ((euclidean__axioms.ET B F D D B C) /\ ((euclidean__axioms.ET B F D C D B) /\ ((euclidean__axioms.ET B F D B C D) /\ (euclidean__axioms.ET B F D B D C))))) as H55.
----------------------------------------------------- exact H54.
----------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.ET B F D D B C) /\ ((euclidean__axioms.ET B F D C D B) /\ ((euclidean__axioms.ET B F D B C D) /\ (euclidean__axioms.ET B F D B D C)))) as H57.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.ET B F D C D B) /\ ((euclidean__axioms.ET B F D B C D) /\ (euclidean__axioms.ET B F D B D C))) as H59.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.ET B F D B C D) /\ (euclidean__axioms.ET B F D B D C)) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [H61 H62].
exact H55.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B D B F D) as H55.
---------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (B) (F) (D) (C) (B) (D) H54).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B D B D F) as H56.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET C B D F D B) /\ ((euclidean__axioms.ET C B D B D F) /\ ((euclidean__axioms.ET C B D F B D) /\ ((euclidean__axioms.ET C B D D F B) /\ (euclidean__axioms.ET C B D D B F))))) as H56.
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (C) (B) (D) (B) (F) (D) H55).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET C B D F D B) /\ ((euclidean__axioms.ET C B D B D F) /\ ((euclidean__axioms.ET C B D F B D) /\ ((euclidean__axioms.ET C B D D F B) /\ (euclidean__axioms.ET C B D D B F))))) as H57.
------------------------------------------------------- exact H56.
------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.ET C B D B D F) /\ ((euclidean__axioms.ET C B D F B D) /\ ((euclidean__axioms.ET C B D D F B) /\ (euclidean__axioms.ET C B D D B F)))) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.ET C B D F B D) /\ ((euclidean__axioms.ET C B D D F B) /\ (euclidean__axioms.ET C B D D B F))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.ET C B D D F B) /\ (euclidean__axioms.ET C B D D B F)) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
exact H59.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C A C B F D) as H57.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.EF E B C A B C D F) /\ ((euclidean__axioms.EF E B C A D C B F) /\ ((euclidean__axioms.EF E B C A C D F B) /\ ((euclidean__axioms.EF E B C A B F D C) /\ ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B))))))) as H57.
------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (E) (B) (C) (A) (F) (B) (C) (D) H24).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF E B C A B C D F) /\ ((euclidean__axioms.EF E B C A D C B F) /\ ((euclidean__axioms.EF E B C A C D F B) /\ ((euclidean__axioms.EF E B C A B F D C) /\ ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B))))))) as H58.
-------------------------------------------------------- exact H57.
-------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.EF E B C A D C B F) /\ ((euclidean__axioms.EF E B C A C D F B) /\ ((euclidean__axioms.EF E B C A B F D C) /\ ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B)))))) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF E B C A C D F B) /\ ((euclidean__axioms.EF E B C A B F D C) /\ ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B))))) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF E B C A B F D C) /\ ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B)))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF E B C A D F B C) /\ ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B))) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF E B C A C B F D) /\ (euclidean__axioms.EF E B C A F D C B)) as H68.
------------------------------------------------------------- exact H67.
------------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF C B F D E B C A) as H58.
------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (E) (B) (C) (A) (C) (B) (F) (D) H57).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF C B F D C B E A) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF C B F D B C A E) /\ ((euclidean__axioms.EF C B F D A C B E) /\ ((euclidean__axioms.EF C B F D C A E B) /\ ((euclidean__axioms.EF C B F D B E A C) /\ ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B))))))) as H59.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (C) (B) (F) (D) (E) (B) (C) (A) H58).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF C B F D B C A E) /\ ((euclidean__axioms.EF C B F D A C B E) /\ ((euclidean__axioms.EF C B F D C A E B) /\ ((euclidean__axioms.EF C B F D B E A C) /\ ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B))))))) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF C B F D A C B E) /\ ((euclidean__axioms.EF C B F D C A E B) /\ ((euclidean__axioms.EF C B F D B E A C) /\ ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B)))))) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF C B F D C A E B) /\ ((euclidean__axioms.EF C B F D B E A C) /\ ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B))))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF C B F D B E A C) /\ ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B)))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF C B F D A E B C) /\ ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.EF C B F D C B E A) /\ (euclidean__axioms.EF C B F D E A C B)) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
exact H70.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF C B E A C B F D) as H60.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (C) (B) (F) (D) (C) (B) (E) (A) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A C B D) as H61.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__halvesofequals (C) (B) (A) (E) (C) (B) (D) (F) (H52) (H43) (H56) (H48) H60).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A D B C) as H62.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET C B A B D C) /\ ((euclidean__axioms.ET C B A C D B) /\ ((euclidean__axioms.ET C B A B C D) /\ ((euclidean__axioms.ET C B A D B C) /\ (euclidean__axioms.ET C B A D C B))))) as H62.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (C) (B) (A) (C) (B) (D) H61).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET C B A B D C) /\ ((euclidean__axioms.ET C B A C D B) /\ ((euclidean__axioms.ET C B A B C D) /\ ((euclidean__axioms.ET C B A D B C) /\ (euclidean__axioms.ET C B A D C B))))) as H63.
------------------------------------------------------------- exact H62.
------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.ET C B A C D B) /\ ((euclidean__axioms.ET C B A B C D) /\ ((euclidean__axioms.ET C B A D B C) /\ (euclidean__axioms.ET C B A D C B)))) as H65.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.ET C B A B C D) /\ ((euclidean__axioms.ET C B A D B C) /\ (euclidean__axioms.ET C B A D C B))) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET C B A D B C) /\ (euclidean__axioms.ET C B A D C B)) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
exact H69.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D B C C B A) as H63.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (C) (B) (A) (D) (B) (C) H62).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET D B C A B C) as H64.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET D B C B A C) /\ ((euclidean__axioms.ET D B C C A B) /\ ((euclidean__axioms.ET D B C B C A) /\ ((euclidean__axioms.ET D B C A B C) /\ (euclidean__axioms.ET D B C A C B))))) as H64.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (D) (B) (C) (C) (B) (A) H63).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET D B C B A C) /\ ((euclidean__axioms.ET D B C C A B) /\ ((euclidean__axioms.ET D B C B C A) /\ ((euclidean__axioms.ET D B C A B C) /\ (euclidean__axioms.ET D B C A C B))))) as H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.ET D B C C A B) /\ ((euclidean__axioms.ET D B C B C A) /\ ((euclidean__axioms.ET D B C A B C) /\ (euclidean__axioms.ET D B C A C B)))) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET D B C B C A) /\ ((euclidean__axioms.ET D B C A B C) /\ (euclidean__axioms.ET D B C A C B))) as H69.
----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.ET D B C A B C) /\ (euclidean__axioms.ET D B C A C B)) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
exact H71.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C D B C) as H65.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (D) (B) (C) (A) (B) (C) H64).
-------------------------------------------------------------- exact H65.
Qed.
