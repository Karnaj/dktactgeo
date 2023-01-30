Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__PGrotate.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__diagonalsmeet.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__34.
Require Export proposition__36.
Definition proposition__38 : forall A B C D E F P Q, (euclidean__defs.Par P Q B C) -> ((euclidean__axioms.Col P Q A) -> ((euclidean__axioms.Col P Q D) -> ((euclidean__axioms.Cong B C E F) -> ((euclidean__axioms.Col B C E) -> ((euclidean__axioms.Col B C F) -> (euclidean__axioms.ET A B C D E F)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (euclidean__defs.Par B C P Q) as H5.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric P Q B C H).
- assert (* Cut *) (euclidean__defs.Par C B P Q) as H6.
-- assert (* Cut *) ((euclidean__defs.Par C B P Q) /\ ((euclidean__defs.Par B C Q P) /\ (euclidean__defs.Par C B Q P))) as H6.
--- apply (@lemma__parallelflip.lemma__parallelflip B C P Q H5).
--- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H7.
-- assert (* Cut *) (exists G, (euclidean__defs.PG A G B C) /\ (euclidean__axioms.Col P Q G)) as H7.
--- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram A B C P Q H6 H0).
--- destruct H7 as [G H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__defs.PG G B C A) as H11.
---- apply (@lemma__PGrotate.lemma__PGrotate A G B C H9).
---- assert (* Cut *) (euclidean__axioms.nCol P B C) as H12.
----- assert (* Cut *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H12.
------ apply (@lemma__parallelNC.lemma__parallelNC P Q B C H).
------ destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
----- assert (* Cut *) (euclidean__axioms.neq B C) as H13.
------ assert (* Cut *) ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq P C) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P)))))) as H13.
------- apply (@lemma__NCdistinct.lemma__NCdistinct P B C H12).
------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H16.
------ assert (* Cut *) (euclidean__axioms.neq E F) as H14.
------- apply (@euclidean__axioms.axiom__nocollapse B C E F H13 H2).
------- assert (* Cut *) (euclidean__defs.Par P Q E F) as H15.
-------- apply (@lemma__collinearparallel2.lemma__collinearparallel2 P Q B C E F H H3 H4 H14).
-------- assert (* Cut *) (euclidean__defs.Par E F P Q) as H16.
--------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric P Q E F H15).
--------- assert (* Cut *) (exists H17, (euclidean__defs.PG D H17 F E) /\ (euclidean__axioms.Col P Q H17)) as H17.
---------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram D F E P Q H16 H1).
---------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__defs.PG H18 F E D) as H22.
----------- apply (@lemma__PGrotate.lemma__PGrotate D H18 F E H20).
----------- assert (* Cut *) (euclidean__axioms.Cong B C F E) as H23.
------------ assert (* Cut *) ((euclidean__axioms.Cong C B F E) /\ ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E))) as H23.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip B C E F H2).
------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H27.
------------ assert (* Cut *) (euclidean__axioms.nCol P Q B) as H24.
------------- assert (* Cut *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H24.
-------------- apply (@lemma__parallelNC.lemma__parallelNC P Q B C H).
-------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H25.
------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H25.
-------------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q B) /\ ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P)))))) as H25.
--------------- apply (@lemma__NCdistinct.lemma__NCdistinct P Q B H24).
--------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H26.
-------------- assert (* Cut *) (euclidean__axioms.Col G A H18) as H26.
--------------- apply (@euclidean__tactics.not__nCol__Col G A H18).
----------------intro H26.
apply (@euclidean__tactics.Col__nCol__False G A H18 H26).
-----------------apply (@lemma__collinear5.lemma__collinear5 P Q G A H18 H25 H10 H0 H21).


--------------- assert (* Cut *) (euclidean__axioms.Col G A D) as H27.
---------------- apply (@euclidean__tactics.not__nCol__Col G A D).
-----------------intro H27.
apply (@euclidean__tactics.Col__nCol__False G A D H27).
------------------apply (@lemma__collinear5.lemma__collinear5 P Q G A D H25 H10 H0 H1).


---------------- assert (* Cut *) (euclidean__axioms.EF G B C A H18 F E D) as H28.
----------------- apply (@proposition__36.proposition__36 G B C A H18 F E D H11 H22 H26 H27 H4 H3 H23).
----------------- assert (* Cut *) (euclidean__axioms.EF G B C A E F H18 D) as H29.
------------------ assert (* Cut *) ((euclidean__axioms.EF G B C A F E D H18) /\ ((euclidean__axioms.EF G B C A D E F H18) /\ ((euclidean__axioms.EF G B C A E D H18 F) /\ ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F))))))) as H29.
------------------- apply (@euclidean__axioms.axiom__EFpermutation G B C A H18 F E D H28).
------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H40.
------------------ assert (* Cut *) (euclidean__axioms.EF E F H18 D G B C A) as H30.
------------------- apply (@euclidean__axioms.axiom__EFsymmetric G B C A E F H18 D H29).
------------------- assert (* Cut *) (euclidean__axioms.EF E F H18 D C B G A) as H31.
-------------------- assert (* Cut *) ((euclidean__axioms.EF E F H18 D B C A G) /\ ((euclidean__axioms.EF E F H18 D A C B G) /\ ((euclidean__axioms.EF E F H18 D C A G B) /\ ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B))))))) as H31.
--------------------- apply (@euclidean__axioms.axiom__EFpermutation E F H18 D G B C A H30).
--------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H42.
-------------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS D M F) /\ (euclidean__axioms.BetS H18 M E)) as H32.
--------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet D H18 F E H20).
--------------------- destruct H32 as [M H33].
destruct H33 as [H34 H35].
assert (* Cut *) (euclidean__axioms.Col D M F) as H36.
---------------------- right.
right.
right.
right.
left.
exact H34.
---------------------- assert (* Cut *) (euclidean__axioms.Col F D M) as H37.
----------------------- assert (* Cut *) ((euclidean__axioms.Col M D F) /\ ((euclidean__axioms.Col M F D) /\ ((euclidean__axioms.Col F D M) /\ ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D))))) as H37.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder D M F H36).
------------------------ destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
----------------------- assert (* Cut *) (exists m, (euclidean__axioms.BetS A m B) /\ (euclidean__axioms.BetS G m C)) as H38.
------------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A G B C H9).
------------------------ destruct H38 as [m H39].
destruct H39 as [H40 H41].
assert (* Cut *) (euclidean__axioms.Col A m B) as H42.
------------------------- right.
right.
right.
right.
left.
exact H40.
------------------------- assert (* Cut *) (euclidean__axioms.Col B A m) as H43.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H43.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder A m B H42).
--------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H48.
-------------------------- assert (* Cut *) (euclidean__defs.Par A G B C) as H44.
--------------------------- destruct H22 as [H44 H45].
destruct H20 as [H46 H47].
destruct H11 as [H48 H49].
destruct H9 as [H50 H51].
exact H50.
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A G B) as H45.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol G B C) /\ (euclidean__axioms.nCol A G C)))) as H45.
----------------------------- apply (@lemma__parallelNC.lemma__parallelNC A G B C H44).
----------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H46.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol B A G) as H46.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A))))) as H46.
------------------------------ apply (@lemma__NCorder.lemma__NCorder A G B H45).
------------------------------ destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H51.
----------------------------- assert (* Cut *) (euclidean__defs.Par D H18 F E) as H47.
------------------------------ destruct H22 as [H47 H48].
destruct H20 as [H49 H50].
destruct H11 as [H51 H52].
destruct H9 as [H53 H54].
exact H49.
------------------------------ assert (* Cut *) (euclidean__axioms.nCol D H18 F) as H48.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D H18 F) /\ ((euclidean__axioms.nCol D F E) /\ ((euclidean__axioms.nCol H18 F E) /\ (euclidean__axioms.nCol D H18 E)))) as H48.
-------------------------------- apply (@lemma__parallelNC.lemma__parallelNC D H18 F E H47).
-------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H49.
------------------------------- assert (* Cut *) (euclidean__axioms.nCol F D H18) as H49.
-------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 D F) /\ ((euclidean__axioms.nCol H18 F D) /\ ((euclidean__axioms.nCol F D H18) /\ ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D))))) as H49.
--------------------------------- apply (@lemma__NCorder.lemma__NCorder D H18 F H48).
--------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H54.
-------------------------------- assert (* Cut *) (euclidean__axioms.TS G B A C) as H50.
--------------------------------- exists m.
split.
---------------------------------- exact H41.
---------------------------------- split.
----------------------------------- exact H43.
----------------------------------- exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A G) as H51.
---------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric B A G C H50).
---------------------------------- assert (* Cut *) (euclidean__axioms.TS H18 F D E) as H52.
----------------------------------- exists M.
split.
------------------------------------ exact H35.
------------------------------------ split.
------------------------------------- exact H37.
------------------------------------- exact H49.
----------------------------------- assert (* Cut *) (euclidean__axioms.TS E F D H18) as H53.
------------------------------------ apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric F D H18 E H52).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 F H18 D D E F) as H54.
------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H54.
-------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
--------------------------------------- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
--------------------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H55.
--------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
---------------------------------------- apply (@H54 A0 B0 C0 D0 __).
---------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H56.
---------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
----------------------------------------- apply (@H55 A0 B0 C0 D0 __).
----------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H57.
----------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
------------------------------------------ apply (@H56 A0 B0 C0 D0 __).
------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------- apply (@H57 H18 D F E H22).
------------------------------------- assert (* Cut *) (euclidean__axioms.ET F H18 D D E F) as H55.
-------------------------------------- apply (@euclidean__axioms.axiom__congruentequal F H18 D D E F H54).
-------------------------------------- assert (* Cut *) (euclidean__axioms.ET F H18 D E F D) as H56.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F H18 D E F D) /\ ((euclidean__axioms.ET F H18 D D F E) /\ ((euclidean__axioms.ET F H18 D E D F) /\ ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E))))) as H56.
---------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F H18 D D E F H55).
---------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H57.
--------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D F H18 D) as H57.
---------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric F H18 D E F D H56).
---------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D F D H18) as H58.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.ET E F D H18 D F) /\ ((euclidean__axioms.ET E F D F D H18) /\ ((euclidean__axioms.ET E F D H18 F D) /\ ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18))))) as H58.
------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation E F D F H18 D H57).
------------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H61.
----------------------------------------- assert (euclidean__defs.PG G B C A) as H59 by exact H11.
assert (* Cut *) (euclidean__axioms.Cong__3 B G A A C B) as H60.
------------------------------------------ assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H60.
------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
-------------------------------------------- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
-------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H61.
-------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
--------------------------------------------- apply (@H60 A0 B0 C0 D0 __).
--------------------------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H62.
--------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
---------------------------------------------- apply (@H61 A0 B0 C0 D0 __).
---------------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H63.
---------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
----------------------------------------------- apply (@H62 A0 B0 C0 D0 __).
----------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------- apply (@H63 G A B C H59).
------------------------------------------ assert (* Cut *) (euclidean__axioms.ET B G A A C B) as H61.
------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal B G A A C B H60).
------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B G A C B A) as H62.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B G A C B A) /\ ((euclidean__axioms.ET B G A A B C) /\ ((euclidean__axioms.ET B G A C A B) /\ ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C))))) as H62.
--------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation B G A A C B H61).
--------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H63.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A B G A) as H63.
--------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric B G A C B A H62).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A B A G) as H64.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET C B A G A B) /\ ((euclidean__axioms.ET C B A B A G) /\ ((euclidean__axioms.ET C B A G B A) /\ ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G))))) as H64.
----------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation C B A B G A H63).
----------------------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H67.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D C B A) as H65.
----------------------------------------------- apply (@euclidean__axioms.axiom__halvesofequals E F D H18 C B A G H58 H53 H64 H51 H31).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D A B C) as H66.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.ET E F D B A C) /\ ((euclidean__axioms.ET E F D C A B) /\ ((euclidean__axioms.ET E F D B C A) /\ ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B))))) as H66.
------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation E F D C B A H65).
------------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A B C E F D) as H67.
------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric E F D A B C H66).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C D E F) as H68.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET A B C F D E) /\ ((euclidean__axioms.ET A B C E D F) /\ ((euclidean__axioms.ET A B C F E D) /\ ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F))))) as H68.
--------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation A B C E F D H67).
--------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
-------------------------------------------------- exact H68.
Qed.
