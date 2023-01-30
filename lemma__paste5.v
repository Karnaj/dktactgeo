Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crisscross.
Require Export lemma__crossimpliesopposite.
Require Export lemma__diagonalsmeet.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__rectangleparallelogram.
Require Export lemma__samenotopposite.
Require Export lemma__sameside2.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__34.
Definition lemma__paste5 : forall B C D E L M b c d e l m, (euclidean__axioms.EF B M L D b m l d) -> ((euclidean__axioms.EF M C E L m c e l) -> ((euclidean__axioms.BetS B M C) -> ((euclidean__axioms.BetS b m c) -> ((euclidean__axioms.BetS E L D) -> ((euclidean__axioms.BetS e l d) -> ((euclidean__defs.RE M C E L) -> ((euclidean__defs.RE m c e l) -> (euclidean__axioms.EF B C E D b c e d)))))))).
Proof.
intro B.
intro C.
intro D.
intro E.
intro L.
intro M.
intro b.
intro c.
intro d.
intro e.
intro l.
intro m.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
assert (* Cut *) (euclidean__defs.PG M C E L) as H7.
- apply (@lemma__rectangleparallelogram.lemma__rectangleparallelogram M C E L H5).
- assert (* Cut *) (euclidean__defs.PG m c e l) as H8.
-- apply (@lemma__rectangleparallelogram.lemma__rectangleparallelogram m c e l H6).
-- assert (* Cut *) (exists P, (euclidean__axioms.BetS M P E) /\ (euclidean__axioms.BetS C P L)) as H9.
--- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet M C E L H7).
--- destruct H9 as [P H10].
destruct H10 as [H11 H12].
assert (* Cut *) (exists p, (euclidean__axioms.BetS m p e) /\ (euclidean__axioms.BetS c p l)) as H13.
---- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet m c e l H8).
---- destruct H13 as [p H14].
destruct H14 as [H15 H16].
assert (* Cut *) (euclidean__defs.Par M C E L) as H17.
----- destruct H8 as [H17 H18].
destruct H7 as [H19 H20].
exact H19.
----- assert (* Cut *) (euclidean__axioms.nCol M C L) as H18.
------ assert (* Cut *) ((euclidean__axioms.nCol M C E) /\ ((euclidean__axioms.nCol M E L) /\ ((euclidean__axioms.nCol C E L) /\ (euclidean__axioms.nCol M C L)))) as H18.
------- apply (@lemma__parallelNC.lemma__parallelNC M C E L H17).
------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H24.
------ assert (* Cut *) (euclidean__defs.Par m c e l) as H19.
------- destruct H8 as [H19 H20].
destruct H7 as [H21 H22].
exact H19.
------- assert (* Cut *) (euclidean__axioms.nCol m c l) as H20.
-------- assert (* Cut *) ((euclidean__axioms.nCol m c e) /\ ((euclidean__axioms.nCol m e l) /\ ((euclidean__axioms.nCol c e l) /\ (euclidean__axioms.nCol m c l)))) as H20.
--------- apply (@lemma__parallelNC.lemma__parallelNC m c e l H19).
--------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H26.
-------- assert (* Cut *) (euclidean__axioms.Cong__3 C M L L E C) as H21.
--------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))))) as H21.
---------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A B0 C0 D0) /\ ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))))) as __0.
----------- apply (@proposition__34.proposition__34 A B0 C0 D0 __).
----------- destruct __0 as [__0 __1].
exact __1.
---------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)))) as H22.
----------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)))) as __0.
------------ apply (@H21 A B0 C0 D0 __).
------------ destruct __0 as [__0 __1].
exact __1.
----------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))) as H23.
------------ intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))) as __0.
------------- apply (@H22 A B0 C0 D0 __).
------------- destruct __0 as [__0 __1].
exact __1.
------------ assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)) as H24.
------------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)) as __0.
-------------- apply (@H23 A B0 C0 D0 __).
-------------- destruct __0 as [__0 __1].
exact __1.
------------- apply (@H24 M L C E H7).
--------- assert (* Cut *) (euclidean__axioms.Cong__3 c m l l e c) as H22.
---------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))))) as H22.
----------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A B0 C0 D0) /\ ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))))) as __0.
------------ apply (@proposition__34.proposition__34 A B0 C0 D0 __).
------------ destruct __0 as [__0 __1].
exact __1.
----------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)))) as H23.
------------ intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A C0 B0 D0) /\ ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)))) as __0.
------------- apply (@H22 A B0 C0 D0 __).
------------- destruct __0 as [__0 __1].
exact __1.
------------ assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))) as H24.
------------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A B0 B0 D0 C0) /\ ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0))) as __0.
-------------- apply (@H23 A B0 C0 D0 __).
-------------- destruct __0 as [__0 __1].
exact __1.
------------- assert (* Cut *) (forall A B0 C0 D0, (euclidean__defs.PG A C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)) as H25.
-------------- intro A.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A B0 D0 D0 C0 A) /\ (euclidean__axioms.Cong__3 C0 A B0 B0 D0 C0)) as __0.
--------------- apply (@H24 A B0 C0 D0 __).
--------------- destruct __0 as [__0 __1].
exact __1.
-------------- apply (@H25 m l c e H8).
---------- assert (* Cut *) (euclidean__axioms.ET C M L L E C) as H23.
----------- apply (@euclidean__axioms.axiom__congruentequal C M L L E C H21).
----------- assert (* Cut *) (euclidean__axioms.ET c m l l e c) as H24.
------------ apply (@euclidean__axioms.axiom__congruentequal c m l l e c H22).
------------ assert (* Cut *) (euclidean__defs.CR M E C L) as H25.
------------- destruct H6 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H5 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H40.
------------- assert (* Cut *) (euclidean__defs.CR m e c l) as H26.
-------------- destruct H6 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H5 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H33.
-------------- assert (* Cut *) (euclidean__axioms.ET c m l c l e) as H27.
--------------- assert (* Cut *) ((euclidean__axioms.ET c m l e c l) /\ ((euclidean__axioms.ET c m l l c e) /\ ((euclidean__axioms.ET c m l e l c) /\ ((euclidean__axioms.ET c m l c e l) /\ (euclidean__axioms.ET c m l c l e))))) as H27.
---------------- apply (@euclidean__axioms.axiom__ETpermutation c m l l e c H24).
---------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H35.
--------------- assert (* Cut *) (euclidean__axioms.ET c l e c m l) as H28.
---------------- apply (@euclidean__axioms.axiom__ETsymmetric c m l c l e H27).
---------------- assert (* Cut *) (euclidean__axioms.ET c l e m c l) as H29.
----------------- assert (* Cut *) ((euclidean__axioms.ET c l e m l c) /\ ((euclidean__axioms.ET c l e c l m) /\ ((euclidean__axioms.ET c l e m c l) /\ ((euclidean__axioms.ET c l e l m c) /\ (euclidean__axioms.ET c l e l c m))))) as H29.
------------------ apply (@euclidean__axioms.axiom__ETpermutation c l e c m l H28).
------------------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H34.
----------------- assert (* Cut *) (euclidean__axioms.ET m c l c l e) as H30.
------------------ apply (@euclidean__axioms.axiom__ETsymmetric c l e m c l H29).
------------------ assert (* Cut *) (euclidean__axioms.ET C M L C L E) as H31.
------------------- assert (* Cut *) ((euclidean__axioms.ET C M L E C L) /\ ((euclidean__axioms.ET C M L L C E) /\ ((euclidean__axioms.ET C M L E L C) /\ ((euclidean__axioms.ET C M L C E L) /\ (euclidean__axioms.ET C M L C L E))))) as H31.
-------------------- apply (@euclidean__axioms.axiom__ETpermutation C M L L E C H23).
-------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H39.
------------------- assert (* Cut *) (euclidean__axioms.ET C L E C M L) as H32.
-------------------- apply (@euclidean__axioms.axiom__ETsymmetric C M L C L E H31).
-------------------- assert (* Cut *) (euclidean__axioms.ET C L E M C L) as H33.
--------------------- assert (* Cut *) ((euclidean__axioms.ET C L E M L C) /\ ((euclidean__axioms.ET C L E C L M) /\ ((euclidean__axioms.ET C L E M C L) /\ ((euclidean__axioms.ET C L E L M C) /\ (euclidean__axioms.ET C L E L C M))))) as H33.
---------------------- apply (@euclidean__axioms.axiom__ETpermutation C L E C M L H32).
---------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H38.
--------------------- assert (* Cut *) (euclidean__axioms.ET M C L C L E) as H34.
---------------------- apply (@euclidean__axioms.axiom__ETsymmetric C L E M C L H33).
---------------------- assert (* Cut *) (euclidean__axioms.TS M C L E) as H35.
----------------------- assert (* Cut *) ((euclidean__axioms.TS M C L E) /\ ((euclidean__axioms.TS M L C E) /\ ((euclidean__axioms.TS E C L M) /\ (euclidean__axioms.TS E L C M)))) as H35.
------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite M E C L H25 H18).
------------------------ destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H36.
----------------------- assert (* Cut *) (euclidean__axioms.TS m c l e) as H36.
------------------------ assert (* Cut *) ((euclidean__axioms.TS m c l e) /\ ((euclidean__axioms.TS m l c e) /\ ((euclidean__axioms.TS e c l m) /\ (euclidean__axioms.TS e l c m)))) as H36.
------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite m e c l H26 H20).
------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H37.
------------------------ assert (* Cut *) (euclidean__axioms.ET M C L m c l) as H37.
------------------------- apply (@euclidean__axioms.axiom__halvesofequals M C L E m c l e H34 H35 H30 H36 H0).
------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L e c m l) as H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.EF M C E L c e l m) /\ ((euclidean__axioms.EF M C E L l e c m) /\ ((euclidean__axioms.EF M C E L e l m c) /\ ((euclidean__axioms.EF M C E L c m l e) /\ ((euclidean__axioms.EF M C E L l m c e) /\ ((euclidean__axioms.EF M C E L e c m l) /\ (euclidean__axioms.EF M C E L m l e c))))))) as H38.
--------------------------- apply (@euclidean__axioms.axiom__EFpermutation M C E L m c e l H0).
--------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H49.
-------------------------- assert (* Cut *) (euclidean__axioms.EF e c m l M C E L) as H39.
--------------------------- apply (@euclidean__axioms.axiom__EFsymmetric M C E L e c m l H38).
--------------------------- assert (* Cut *) (euclidean__axioms.EF e c m l E C M L) as H40.
---------------------------- assert (* Cut *) ((euclidean__axioms.EF e c m l C E L M) /\ ((euclidean__axioms.EF e c m l L E C M) /\ ((euclidean__axioms.EF e c m l E L M C) /\ ((euclidean__axioms.EF e c m l C M L E) /\ ((euclidean__axioms.EF e c m l L M C E) /\ ((euclidean__axioms.EF e c m l E C M L) /\ (euclidean__axioms.EF e c m l M L E C))))))) as H40.
----------------------------- apply (@euclidean__axioms.axiom__EFpermutation e c m l M C E L H39).
----------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H51.
---------------------------- assert (* Cut *) (euclidean__axioms.EF E C M L e c m l) as H41.
----------------------------- apply (@euclidean__axioms.axiom__EFsymmetric e c m l E C M L H40).
----------------------------- assert (* Cut *) (euclidean__axioms.TS E C L M) as H42.
------------------------------ apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric C L M E H35).
------------------------------ assert (* Cut *) (euclidean__axioms.TS e c l m) as H43.
------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric c l m e H36).
------------------------------- assert (* Cut *) (euclidean__axioms.ET M C L E C L) as H44.
-------------------------------- assert (* Cut *) ((euclidean__axioms.ET M C L L E C) /\ ((euclidean__axioms.ET M C L C E L) /\ ((euclidean__axioms.ET M C L L C E) /\ ((euclidean__axioms.ET M C L E L C) /\ (euclidean__axioms.ET M C L E C L))))) as H44.
--------------------------------- apply (@euclidean__axioms.axiom__ETpermutation M C L C L E H34).
--------------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
-------------------------------- assert (* Cut *) (euclidean__axioms.ET E C L M C L) as H45.
--------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric M C L E C L H44).
--------------------------------- assert (* Cut *) (euclidean__axioms.ET E C L C L M) as H46.
---------------------------------- assert (* Cut *) ((euclidean__axioms.ET E C L C L M) /\ ((euclidean__axioms.ET E C L M L C) /\ ((euclidean__axioms.ET E C L C M L) /\ ((euclidean__axioms.ET E C L L C M) /\ (euclidean__axioms.ET E C L L M C))))) as H46.
----------------------------------- apply (@euclidean__axioms.axiom__ETpermutation E C L M C L H45).
----------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H47.
---------------------------------- assert (* Cut *) (euclidean__axioms.ET m c l e c l) as H47.
----------------------------------- assert (* Cut *) ((euclidean__axioms.ET m c l l e c) /\ ((euclidean__axioms.ET m c l c e l) /\ ((euclidean__axioms.ET m c l l c e) /\ ((euclidean__axioms.ET m c l e l c) /\ (euclidean__axioms.ET m c l e c l))))) as H47.
------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation m c l c l e H30).
------------------------------------ destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
----------------------------------- assert (* Cut *) (euclidean__axioms.ET e c l m c l) as H48.
------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric m c l e c l H47).
------------------------------------ assert (* Cut *) (euclidean__axioms.ET e c l c l m) as H49.
------------------------------------- assert (* Cut *) ((euclidean__axioms.ET e c l c l m) /\ ((euclidean__axioms.ET e c l m l c) /\ ((euclidean__axioms.ET e c l c m l) /\ ((euclidean__axioms.ET e c l l c m) /\ (euclidean__axioms.ET e c l l m c))))) as H49.
-------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation e c l m c l H48).
-------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H50.
------------------------------------- assert (* Cut *) (euclidean__axioms.ET E C L e c l) as H50.
-------------------------------------- apply (@euclidean__axioms.axiom__halvesofequals E C L M e c l m H46 H42 H49 H43 H41).
-------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D d b m l) as H51.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B M L D m l d b) /\ ((euclidean__axioms.EF B M L D d l m b) /\ ((euclidean__axioms.EF B M L D l d b m) /\ ((euclidean__axioms.EF B M L D m b d l) /\ ((euclidean__axioms.EF B M L D d b m l) /\ ((euclidean__axioms.EF B M L D l m b d) /\ (euclidean__axioms.EF B M L D b d l m))))))) as H51.
---------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation B M L D b m l d H).
---------------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
--------------------------------------- assert (* Cut *) (euclidean__axioms.EF d b m l B M L D) as H52.
---------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric B M L D d b m l H51).
---------------------------------------- assert (* Cut *) (euclidean__axioms.EF d b m l D B M L) as H53.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.EF d b m l M L D B) /\ ((euclidean__axioms.EF d b m l D L M B) /\ ((euclidean__axioms.EF d b m l L D B M) /\ ((euclidean__axioms.EF d b m l M B D L) /\ ((euclidean__axioms.EF d b m l D B M L) /\ ((euclidean__axioms.EF d b m l L M B D) /\ (euclidean__axioms.EF d b m l B D L M))))))) as H53.
------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation d b m l B M L D H52).
------------------------------------------ destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H62.
----------------------------------------- assert (* Cut *) (euclidean__axioms.EF D B M L d b m l) as H54.
------------------------------------------ apply (@euclidean__axioms.axiom__EFsymmetric d b m l D B M L H53).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B M C) as H55.
------------------------------------------- right.
right.
right.
right.
left.
exact H1.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M C B) as H56.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H56.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M C H55).
--------------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H59.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H57.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B C))) as H57.
---------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B M C H1).
---------------------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H61.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Par E L M C) as H58.
---------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric M C E L H17).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Par E L B C) as H59.
----------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E L B M C H58 H56 H57).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C E L) as H60.
------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E L B C H59).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E L D) as H61.
------------------------------------------------- right.
right.
right.
right.
left.
exact H3.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L D) as H62.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq L D) /\ ((euclidean__axioms.neq E L) /\ (euclidean__axioms.neq E D))) as H62.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E L D H3).
--------------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H63.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D L) as H63.
--------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric L D H62).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C D L) as H64.
---------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel B C D E L H60 H61 H63).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E L) as H65.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq L D) /\ ((euclidean__axioms.neq E L) /\ (euclidean__axioms.neq E D))) as H65.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E L D H3).
------------------------------------------------------ destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M C) as H66.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B C))) as H66.
------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B M C H1).
------------------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H67.
------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.CR B D C L)) as H67.
------------------------------------------------------- intro H67.
assert (* Cut *) (~(euclidean__axioms.Col C L M)) as H68.
-------------------------------------------------------- intro H68.
assert (* Cut *) (euclidean__axioms.Col M C L) as H69.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col L C M) /\ ((euclidean__axioms.Col L M C) /\ ((euclidean__axioms.Col M C L) /\ ((euclidean__axioms.Col C M L) /\ (euclidean__axioms.Col M L C))))) as H69.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C L M H68).
---------------------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H74.
--------------------------------------------------------- assert (* Cut *) (L = L) as H70.
---------------------------------------------------------- apply (@logic.eq__refl Point L).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E L L) as H71.
----------------------------------------------------------- right.
right.
left.
exact H70.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E L M C) as H72.
------------------------------------------------------------ exists L.
split.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- exact H69.
------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.Meet E L M C)) as H73.
------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H73 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H73.
destruct __TmpHyp as [x H74].
destruct H74 as [x0 H75].
destruct H75 as [x1 H76].
destruct H76 as [x2 H77].
destruct H77 as [x3 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H99 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H99.
destruct __TmpHyp0 as [x4 H100].
destruct H100 as [x5 H101].
destruct H101 as [x6 H102].
destruct H102 as [x7 H103].
destruct H103 as [x8 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H125 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H125.
destruct __TmpHyp1 as [x9 H126].
destruct H126 as [x10 H127].
destruct H127 as [x11 H128].
destruct H128 as [x12 H129].
destruct H129 as [x13 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H151 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H151.
destruct __TmpHyp2 as [x14 H152].
destruct H152 as [x15 H153].
destruct H153 as [x16 H154].
destruct H154 as [x17 H155].
destruct H155 as [x18 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H177 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H177.
destruct __TmpHyp3 as [x19 H178].
destruct H178 as [x20 H179].
destruct H179 as [x21 H180].
destruct H180 as [x22 H181].
destruct H181 as [x23 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H203 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H203.
destruct __TmpHyp4 as [x24 H204].
destruct H204 as [x25 H205].
destruct H205 as [x26 H206].
destruct H206 as [x27 H207].
destruct H207 as [x28 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
exact H173.
------------------------------------------------------------- apply (@H73 H72).
-------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C L D)) as H69.
--------------------------------------------------------- intro H69.
assert (* Cut *) (euclidean__axioms.Col D L C) as H70.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col L C D) /\ ((euclidean__axioms.Col L D C) /\ ((euclidean__axioms.Col D C L) /\ ((euclidean__axioms.Col C D L) /\ (euclidean__axioms.Col D L C))))) as H70.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C L D H69).
----------------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
---------------------------------------------------------- assert (euclidean__axioms.Col E L D) as H71 by exact H61.
assert (* Cut *) (euclidean__axioms.Col D L E) as H72.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col E D L) /\ (euclidean__axioms.Col D L E))))) as H72.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E L D H71).
------------------------------------------------------------ destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H80.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L D) as H73.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq p l) /\ ((euclidean__axioms.neq c p) /\ (euclidean__axioms.neq c l))) as H73.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c p l H16).
------------------------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H62.
------------------------------------------------------------ assert (euclidean__axioms.neq D L) as H74 by exact H63.
assert (* Cut *) (euclidean__axioms.Col L E C) as H75.
------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col L E C).
--------------------------------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False L E C H75).
---------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D L E C H72 H70 H74).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E L C) as H76.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E L C) /\ ((euclidean__axioms.Col E C L) /\ ((euclidean__axioms.Col C L E) /\ ((euclidean__axioms.Col L C E) /\ (euclidean__axioms.Col C E L))))) as H76.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder L E C H75).
--------------------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H77.
-------------------------------------------------------------- assert (* Cut *) (C = C) as H77.
--------------------------------------------------------------- apply (@logic.eq__refl Point C).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M C C) as H78.
---------------------------------------------------------------- right.
right.
left.
exact H77.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E L M C) as H79.
----------------------------------------------------------------- exists C.
split.
------------------------------------------------------------------ exact H65.
------------------------------------------------------------------ split.
------------------------------------------------------------------- exact H66.
------------------------------------------------------------------- split.
-------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------- exact H78.
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E L M C)) as H80.
------------------------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H80.
destruct __TmpHyp as [x H81].
destruct H81 as [x0 H82].
destruct H82 as [x1 H83].
destruct H83 as [x2 H84].
destruct H84 as [x3 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H106 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H106.
destruct __TmpHyp0 as [x4 H107].
destruct H107 as [x5 H108].
destruct H108 as [x6 H109].
destruct H109 as [x7 H110].
destruct H110 as [x8 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H132 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H132.
destruct __TmpHyp1 as [x9 H133].
destruct H133 as [x10 H134].
destruct H134 as [x11 H135].
destruct H135 as [x12 H136].
destruct H136 as [x13 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H158 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H158.
destruct __TmpHyp2 as [x14 H159].
destruct H159 as [x15 H160].
destruct H160 as [x16 H161].
destruct H161 as [x17 H162].
destruct H162 as [x18 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H184 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H184.
destruct __TmpHyp3 as [x19 H185].
destruct H185 as [x20 H186].
destruct H186 as [x21 H187].
destruct H187 as [x22 H188].
destruct H188 as [x23 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H210 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H210.
destruct __TmpHyp4 as [x24 H211].
destruct H211 as [x25 H212].
destruct H212 as [x26 H213].
destruct H213 as [x27 H214].
destruct H214 as [x28 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
exact H180.
------------------------------------------------------------------ apply (@H68).
-------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col C L M).
--------------------------------------------------------------------intro H81.
apply (@H80 H79).


--------------------------------------------------------- assert (* Cut *) (L = L) as H70.
---------------------------------------------------------- apply (@logic.eq__refl Point L).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C L L) as H71.
----------------------------------------------------------- right.
right.
left.
exact H70.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D L E) as H72.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry E L D H3).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C L P) as H73.
------------------------------------------------------------- right.
right.
right.
right.
right.
exact H12.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS D M C L) as H74.
-------------------------------------------------------------- exists E.
exists L.
exists P.
split.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H73.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H11.
------------------------------------------------------------------ split.
------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol C L D H69).
------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol C L M H68).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C M B) as H75.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B M C H1).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C M) as H76.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H76.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M B H75).
----------------------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H79.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C M B) as H77.
----------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C M B).
------------------------------------------------------------------right.
right.
exact H75.

------------------------------------------------------------------ exact H76.
----------------------------------------------------------------- assert (* Cut *) (C = C) as H78.
------------------------------------------------------------------ apply (@logic.eq__refl Point C).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C C L) as H79.
------------------------------------------------------------------- left.
exact H78.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS D B C L) as H80.
-------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 C C L D M B H74 H79 H77).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS B D C L) as H81.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS B D C L) /\ ((euclidean__defs.OS D B L C) /\ (euclidean__defs.OS B D L C))) as H81.
---------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C L D B H80).
---------------------------------------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H82.
--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.TS B C L D)) as H82.
---------------------------------------------------------------------- apply (@lemma__samenotopposite.lemma__samenotopposite B D C L H81).
---------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C L)) as H83.
----------------------------------------------------------------------- intro H83.
assert (euclidean__axioms.Col B M C) as H84 by exact H55.
assert (* Cut *) (euclidean__axioms.Col B C M) as H85.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H85.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M C H84).
------------------------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H92.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H86.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H86.
-------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M B H75).
-------------------------------------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H57.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C M L) as H87.
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C M L).
---------------------------------------------------------------------------intro H87.
apply (@H68).
----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 B C L M H83 H85 H86).


-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M C L) as H88.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M C L) /\ ((euclidean__axioms.Col M L C) /\ ((euclidean__axioms.Col L C M) /\ ((euclidean__axioms.Col C L M) /\ (euclidean__axioms.Col L M C))))) as H88.
---------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C M L H87).
---------------------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H89.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E L L) as H89.
---------------------------------------------------------------------------- right.
right.
left.
exact H70.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E L M C) as H90.
----------------------------------------------------------------------------- exists L.
split.
------------------------------------------------------------------------------ exact H65.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E L M C)) as H91.
------------------------------------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H91 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H91.
destruct __TmpHyp as [x H92].
destruct H92 as [x0 H93].
destruct H93 as [x1 H94].
destruct H94 as [x2 H95].
destruct H95 as [x3 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H117 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H117.
destruct __TmpHyp0 as [x4 H118].
destruct H118 as [x5 H119].
destruct H119 as [x6 H120].
destruct H120 as [x7 H121].
destruct H121 as [x8 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H143 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H143.
destruct __TmpHyp1 as [x9 H144].
destruct H144 as [x10 H145].
destruct H145 as [x11 H146].
destruct H146 as [x12 H147].
destruct H147 as [x13 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H169 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H169.
destruct __TmpHyp2 as [x14 H170].
destruct H170 as [x15 H171].
destruct H171 as [x16 H172].
destruct H172 as [x17 H173].
destruct H173 as [x18 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H195 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H195.
destruct __TmpHyp3 as [x19 H196].
destruct H196 as [x20 H197].
destruct H197 as [x21 H198].
destruct H198 as [x22 H199].
destruct H199 as [x23 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H221 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H221.
destruct __TmpHyp4 as [x24 H222].
destruct H222 as [x25 H223].
destruct H223 as [x26 H224].
destruct H224 as [x27 H225].
destruct H225 as [x28 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
exact H191.
------------------------------------------------------------------------------ apply (@H68).
-------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col C L M).
--------------------------------------------------------------------------------intro H92.
apply (@H91 H90).


----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B C L D) as H84.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR B D C L) -> ((euclidean__axioms.nCol B C L) -> (euclidean__axioms.TS B C L D))) as H84.
------------------------------------------------------------------------- intro __.
intro __0.
assert (* AndElim *) ((euclidean__axioms.TS B C L D) /\ ((euclidean__axioms.TS B L C D) /\ ((euclidean__axioms.TS D C L B) /\ (euclidean__axioms.TS D L C B)))) as __1.
-------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite B D C L __ __0).
-------------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
------------------------------------------------------------------------- apply (@H84 H67).
--------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol B C L H83).

------------------------------------------------------------------------ apply (@H68).
-------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col C L M).
--------------------------------------------------------------------------intro H85.
apply (@H82 H84).


------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR B L D C) as H68.
-------------------------------------------------------- apply (@lemma__crisscross.lemma__crisscross B D C L H64 H67).
-------------------------------------------------------- assert (exists R, (euclidean__axioms.BetS B R L) /\ (euclidean__axioms.BetS D R C)) as H69 by exact H68.
destruct H69 as [R H70].
destruct H70 as [H71 H72].
assert (* Cut *) (euclidean__axioms.Col b m c) as H73.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H2.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m c b) as H74.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m b c) /\ ((euclidean__axioms.Col m c b) /\ ((euclidean__axioms.Col c b m) /\ ((euclidean__axioms.Col b c m) /\ (euclidean__axioms.Col c m b))))) as H74.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder b m c H73).
----------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H77.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b c) as H75.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H75.
------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal b m c H2).
------------------------------------------------------------ destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H79.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par e l m c) as H76.
------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric m c e l H19).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par e l b c) as H77.
------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel e l b m c H76 H74 H75).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par b c e l) as H78.
-------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric e l b c H77).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e l d) as H79.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H4.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq l d) as H80.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq l d) /\ ((euclidean__axioms.neq e l) /\ (euclidean__axioms.neq e d))) as H80.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal e l d H4).
----------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H81.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq d l) as H81.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric l d H80).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par b c d l) as H82.
------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel b c d e l H78 H79 H81).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq e l) as H83.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq l d) /\ ((euclidean__axioms.neq e l) /\ (euclidean__axioms.neq e d))) as H83.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal e l d H4).
-------------------------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H86.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m c) as H84.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H84.
--------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal b m c H2).
--------------------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H85.
-------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.CR b d c l)) as H85.
--------------------------------------------------------------------- intro H85.
assert (* Cut *) (~(euclidean__axioms.Col c l m)) as H86.
---------------------------------------------------------------------- intro H86.
assert (* Cut *) (euclidean__axioms.Col m c l) as H87.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col l c m) /\ ((euclidean__axioms.Col l m c) /\ ((euclidean__axioms.Col m c l) /\ ((euclidean__axioms.Col c m l) /\ (euclidean__axioms.Col m l c))))) as H87.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder c l m H86).
------------------------------------------------------------------------ destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H92.
----------------------------------------------------------------------- assert (* Cut *) (l = l) as H88.
------------------------------------------------------------------------ apply (@logic.eq__refl Point l).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col e l l) as H89.
------------------------------------------------------------------------- right.
right.
left.
exact H88.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet e l m c) as H90.
-------------------------------------------------------------------------- exists l.
split.
--------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet e l m c)) as H91.
--------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H91 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H91.
destruct __TmpHyp as [x H92].
destruct H92 as [x0 H93].
destruct H93 as [x1 H94].
destruct H94 as [x2 H95].
destruct H95 as [x3 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H117 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H117.
destruct __TmpHyp0 as [x4 H118].
destruct H118 as [x5 H119].
destruct H119 as [x6 H120].
destruct H120 as [x7 H121].
destruct H121 as [x8 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H143 by exact H77.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H143.
destruct __TmpHyp1 as [x9 H144].
destruct H144 as [x10 H145].
destruct H145 as [x11 H146].
destruct H146 as [x12 H147].
destruct H147 as [x13 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H169 by exact H76.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H169.
destruct __TmpHyp2 as [x14 H170].
destruct H170 as [x15 H171].
destruct H171 as [x16 H172].
destruct H172 as [x17 H173].
destruct H173 as [x18 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H195 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H195.
destruct __TmpHyp3 as [x19 H196].
destruct H196 as [x20 H197].
destruct H197 as [x21 H198].
destruct H198 as [x22 H199].
destruct H199 as [x23 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H221 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H221.
destruct __TmpHyp4 as [x24 H222].
destruct H222 as [x25 H223].
destruct H223 as [x26 H224].
destruct H224 as [x27 H225].
destruct H225 as [x28 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H247 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H247.
destruct __TmpHyp5 as [x29 H248].
destruct H248 as [x30 H249].
destruct H249 as [x31 H250].
destruct H250 as [x32 H251].
destruct H251 as [x33 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
destruct H264 as [H265 H266].
destruct H266 as [H267 H268].
destruct H268 as [H269 H270].
destruct H270 as [H271 H272].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H273 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H273.
destruct __TmpHyp6 as [x34 H274].
destruct H274 as [x35 H275].
destruct H275 as [x36 H276].
destruct H276 as [x37 H277].
destruct H277 as [x38 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
destruct H290 as [H291 H292].
destruct H292 as [H293 H294].
destruct H294 as [H295 H296].
destruct H296 as [H297 H298].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H299 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H299.
destruct __TmpHyp7 as [x39 H300].
destruct H300 as [x40 H301].
destruct H301 as [x41 H302].
destruct H302 as [x42 H303].
destruct H303 as [x43 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
destruct H314 as [H315 H316].
destruct H316 as [H317 H318].
destruct H318 as [H319 H320].
destruct H320 as [H321 H322].
destruct H322 as [H323 H324].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H325 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H325.
destruct __TmpHyp8 as [x44 H326].
destruct H326 as [x45 H327].
destruct H327 as [x46 H328].
destruct H328 as [x47 H329].
destruct H329 as [x48 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
destruct H336 as [H337 H338].
destruct H338 as [H339 H340].
destruct H340 as [H341 H342].
destruct H342 as [H343 H344].
destruct H344 as [H345 H346].
destruct H346 as [H347 H348].
destruct H348 as [H349 H350].
exact H191.
--------------------------------------------------------------------------- apply (@H91 H90).
---------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col c l d)) as H87.
----------------------------------------------------------------------- intro H87.
assert (* Cut *) (euclidean__axioms.Col d l c) as H88.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col l c d) /\ ((euclidean__axioms.Col l d c) /\ ((euclidean__axioms.Col d c l) /\ ((euclidean__axioms.Col c d l) /\ (euclidean__axioms.Col d l c))))) as H88.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder c l d H87).
------------------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H96.
------------------------------------------------------------------------ assert (euclidean__axioms.Col e l d) as H89 by exact H79.
assert (* Cut *) (euclidean__axioms.Col d l e) as H90.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col l e d) /\ ((euclidean__axioms.Col l d e) /\ ((euclidean__axioms.Col d e l) /\ ((euclidean__axioms.Col e d l) /\ (euclidean__axioms.Col d l e))))) as H90.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder e l d H89).
-------------------------------------------------------------------------- destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H98.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq l d) as H91.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq D R) /\ (euclidean__axioms.neq D C))) as H91.
--------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D R C H72).
--------------------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H80.
-------------------------------------------------------------------------- assert (euclidean__axioms.neq d l) as H92 by exact H81.
assert (* Cut *) (euclidean__axioms.Col l e c) as H93.
--------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col l e c).
----------------------------------------------------------------------------intro H93.
apply (@euclidean__tactics.Col__nCol__False l e c H93).
-----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 d l e c H90 H88 H92).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e l c) as H94.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e l c) /\ ((euclidean__axioms.Col e c l) /\ ((euclidean__axioms.Col c l e) /\ ((euclidean__axioms.Col l c e) /\ (euclidean__axioms.Col c e l))))) as H94.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder l e c H93).
----------------------------------------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H95.
---------------------------------------------------------------------------- assert (* Cut *) (c = c) as H95.
----------------------------------------------------------------------------- apply (@logic.eq__refl Point c).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m c c) as H96.
------------------------------------------------------------------------------ right.
right.
left.
exact H95.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet e l m c) as H97.
------------------------------------------------------------------------------- exists c.
split.
-------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet e l m c)) as H98.
-------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H98 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H98.
destruct __TmpHyp as [x H99].
destruct H99 as [x0 H100].
destruct H100 as [x1 H101].
destruct H101 as [x2 H102].
destruct H102 as [x3 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H124 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H124.
destruct __TmpHyp0 as [x4 H125].
destruct H125 as [x5 H126].
destruct H126 as [x6 H127].
destruct H127 as [x7 H128].
destruct H128 as [x8 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H150 by exact H77.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H150.
destruct __TmpHyp1 as [x9 H151].
destruct H151 as [x10 H152].
destruct H152 as [x11 H153].
destruct H153 as [x12 H154].
destruct H154 as [x13 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H176 by exact H76.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H176.
destruct __TmpHyp2 as [x14 H177].
destruct H177 as [x15 H178].
destruct H178 as [x16 H179].
destruct H179 as [x17 H180].
destruct H180 as [x18 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H202 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H202.
destruct __TmpHyp3 as [x19 H203].
destruct H203 as [x20 H204].
destruct H204 as [x21 H205].
destruct H205 as [x22 H206].
destruct H206 as [x23 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H228 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H228.
destruct __TmpHyp4 as [x24 H229].
destruct H229 as [x25 H230].
destruct H230 as [x26 H231].
destruct H231 as [x27 H232].
destruct H232 as [x28 H233].
destruct H233 as [H234 H235].
destruct H235 as [H236 H237].
destruct H237 as [H238 H239].
destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
destruct H249 as [H250 H251].
destruct H251 as [H252 H253].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H254 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H254.
destruct __TmpHyp5 as [x29 H255].
destruct H255 as [x30 H256].
destruct H256 as [x31 H257].
destruct H257 as [x32 H258].
destruct H258 as [x33 H259].
destruct H259 as [H260 H261].
destruct H261 as [H262 H263].
destruct H263 as [H264 H265].
destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
destruct H277 as [H278 H279].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H280 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H280.
destruct __TmpHyp6 as [x34 H281].
destruct H281 as [x35 H282].
destruct H282 as [x36 H283].
destruct H283 as [x37 H284].
destruct H284 as [x38 H285].
destruct H285 as [H286 H287].
destruct H287 as [H288 H289].
destruct H289 as [H290 H291].
destruct H291 as [H292 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
destruct H303 as [H304 H305].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H306 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H306.
destruct __TmpHyp7 as [x39 H307].
destruct H307 as [x40 H308].
destruct H308 as [x41 H309].
destruct H309 as [x42 H310].
destruct H310 as [x43 H311].
destruct H311 as [H312 H313].
destruct H313 as [H314 H315].
destruct H315 as [H316 H317].
destruct H317 as [H318 H319].
destruct H319 as [H320 H321].
destruct H321 as [H322 H323].
destruct H323 as [H324 H325].
destruct H325 as [H326 H327].
destruct H327 as [H328 H329].
destruct H329 as [H330 H331].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H332 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H332.
destruct __TmpHyp8 as [x44 H333].
destruct H333 as [x45 H334].
destruct H334 as [x46 H335].
destruct H335 as [x47 H336].
destruct H336 as [x48 H337].
destruct H337 as [H338 H339].
destruct H339 as [H340 H341].
destruct H341 as [H342 H343].
destruct H343 as [H344 H345].
destruct H345 as [H346 H347].
destruct H347 as [H348 H349].
destruct H349 as [H350 H351].
destruct H351 as [H352 H353].
destruct H353 as [H354 H355].
destruct H355 as [H356 H357].
exact H198.
-------------------------------------------------------------------------------- apply (@H86).
---------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col c l m).
----------------------------------------------------------------------------------intro H99.
apply (@H98 H97).


----------------------------------------------------------------------- assert (* Cut *) (l = l) as H88.
------------------------------------------------------------------------ apply (@logic.eq__refl Point l).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col c l l) as H89.
------------------------------------------------------------------------- right.
right.
left.
exact H88.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS d l e) as H90.
-------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry e l d H4).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c l p) as H91.
--------------------------------------------------------------------------- right.
right.
right.
right.
right.
exact H16.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS d m c l) as H92.
---------------------------------------------------------------------------- exists e.
exists l.
exists p.
split.
----------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H15.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol c l d H87).
--------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol c l m H86).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS c m b) as H93.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry b m c H2).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq c m) as H94.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m b) /\ ((euclidean__axioms.neq c m) /\ (euclidean__axioms.neq c b))) as H94.
------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c m b H93).
------------------------------------------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H97.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out c m b) as H95.
------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 c m b).
--------------------------------------------------------------------------------right.
right.
exact H93.

-------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- assert (* Cut *) (c = c) as H96.
-------------------------------------------------------------------------------- apply (@logic.eq__refl Point c).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c c l) as H97.
--------------------------------------------------------------------------------- left.
exact H96.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS d b c l) as H98.
---------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 c c l d m b H92 H97 H95).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS b d c l) as H99.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS b d c l) /\ ((euclidean__defs.OS d b l c) /\ (euclidean__defs.OS b d l c))) as H99.
------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric c l d b H98).
------------------------------------------------------------------------------------ destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H100.
----------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.TS b c l d)) as H100.
------------------------------------------------------------------------------------ apply (@lemma__samenotopposite.lemma__samenotopposite b d c l H99).
------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col b c l)) as H101.
------------------------------------------------------------------------------------- intro H101.
assert (euclidean__axioms.Col b m c) as H102 by exact H73.
assert (* Cut *) (euclidean__axioms.Col b c m) as H103.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m b c) /\ ((euclidean__axioms.Col m c b) /\ ((euclidean__axioms.Col c b m) /\ ((euclidean__axioms.Col b c m) /\ (euclidean__axioms.Col c m b))))) as H103.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder b m c H102).
--------------------------------------------------------------------------------------- destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
exact H110.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b c) as H104.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m b) /\ ((euclidean__axioms.neq c m) /\ (euclidean__axioms.neq c b))) as H104.
---------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c m b H93).
---------------------------------------------------------------------------------------- destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
exact H75.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c m l) as H105.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col c m l).
-----------------------------------------------------------------------------------------intro H105.
apply (@H86).
------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 b c l m H101 H103 H104).


---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m c l) as H106.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m c l) /\ ((euclidean__axioms.Col m l c) /\ ((euclidean__axioms.Col l c m) /\ ((euclidean__axioms.Col c l m) /\ (euclidean__axioms.Col l m c))))) as H106.
------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder c m l H105).
------------------------------------------------------------------------------------------ destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H107.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e l l) as H107.
------------------------------------------------------------------------------------------ right.
right.
left.
exact H88.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet e l m c) as H108.
------------------------------------------------------------------------------------------- exists l.
split.
-------------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet e l m c)) as H109.
-------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H109 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H109.
destruct __TmpHyp as [x H110].
destruct H110 as [x0 H111].
destruct H111 as [x1 H112].
destruct H112 as [x2 H113].
destruct H113 as [x3 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H135 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H135.
destruct __TmpHyp0 as [x4 H136].
destruct H136 as [x5 H137].
destruct H137 as [x6 H138].
destruct H138 as [x7 H139].
destruct H139 as [x8 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H161 by exact H77.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H161.
destruct __TmpHyp1 as [x9 H162].
destruct H162 as [x10 H163].
destruct H163 as [x11 H164].
destruct H164 as [x12 H165].
destruct H165 as [x13 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H187 by exact H76.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H187.
destruct __TmpHyp2 as [x14 H188].
destruct H188 as [x15 H189].
destruct H189 as [x16 H190].
destruct H190 as [x17 H191].
destruct H191 as [x18 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H213 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H213.
destruct __TmpHyp3 as [x19 H214].
destruct H214 as [x20 H215].
destruct H215 as [x21 H216].
destruct H216 as [x22 H217].
destruct H217 as [x23 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H239 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H239.
destruct __TmpHyp4 as [x24 H240].
destruct H240 as [x25 H241].
destruct H241 as [x26 H242].
destruct H242 as [x27 H243].
destruct H243 as [x28 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H265 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H265.
destruct __TmpHyp5 as [x29 H266].
destruct H266 as [x30 H267].
destruct H267 as [x31 H268].
destruct H268 as [x32 H269].
destruct H269 as [x33 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H291 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H291.
destruct __TmpHyp6 as [x34 H292].
destruct H292 as [x35 H293].
destruct H293 as [x36 H294].
destruct H294 as [x37 H295].
destruct H295 as [x38 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
destruct H314 as [H315 H316].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H317 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H317.
destruct __TmpHyp7 as [x39 H318].
destruct H318 as [x40 H319].
destruct H319 as [x41 H320].
destruct H320 as [x42 H321].
destruct H321 as [x43 H322].
destruct H322 as [H323 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
destruct H336 as [H337 H338].
destruct H338 as [H339 H340].
destruct H340 as [H341 H342].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H343 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H343.
destruct __TmpHyp8 as [x44 H344].
destruct H344 as [x45 H345].
destruct H345 as [x46 H346].
destruct H346 as [x47 H347].
destruct H347 as [x48 H348].
destruct H348 as [H349 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
destruct H360 as [H361 H362].
destruct H362 as [H363 H364].
destruct H364 as [H365 H366].
destruct H366 as [H367 H368].
exact H209.
-------------------------------------------------------------------------------------------- apply (@H86).
---------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col c l m).
----------------------------------------------------------------------------------------------intro H110.
apply (@H109 H108).


------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS b c l d) as H102.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR b d c l) -> ((euclidean__axioms.nCol b c l) -> (euclidean__axioms.TS b c l d))) as H102.
--------------------------------------------------------------------------------------- intro __.
intro __0.
assert (* AndElim *) ((euclidean__axioms.TS b c l d) /\ ((euclidean__axioms.TS b l c d) /\ ((euclidean__axioms.TS d c l b) /\ (euclidean__axioms.TS d l c b)))) as __1.
---------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite b d c l __ __0).
---------------------------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
--------------------------------------------------------------------------------------- apply (@H102 H85).
----------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol b c l H101).

-------------------------------------------------------------------------------------- apply (@H86).
---------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col c l m).
----------------------------------------------------------------------------------------intro H103.
apply (@H100 H102).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR b l d c) as H86.
---------------------------------------------------------------------- apply (@lemma__crisscross.lemma__crisscross b d c l H82 H85).
---------------------------------------------------------------------- assert (exists r, (euclidean__axioms.BetS b r l) /\ (euclidean__axioms.BetS d r c)) as H87 by exact H86.
destruct H87 as [r H88].
destruct H88 as [H89 H90].
assert (* Cut *) (euclidean__axioms.EF D B C L d b c l) as H91.
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste2 D B M C L R d b m c l r H1 H2 H37 H54 H72 H71 H90 H89).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF D B C L b d l c) as H92.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.EF D B C L b c l d) /\ ((euclidean__axioms.EF D B C L l c b d) /\ ((euclidean__axioms.EF D B C L c l d b) /\ ((euclidean__axioms.EF D B C L b d l c) /\ ((euclidean__axioms.EF D B C L l d b c) /\ ((euclidean__axioms.EF D B C L c b d l) /\ (euclidean__axioms.EF D B C L d l c b))))))) as H92.
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation D B C L d b c l H91).
------------------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H99.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF b d l c D B C L) as H93.
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric D B C L b d l c H92).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF b d l c B D L C) as H94.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF b d l c B C L D) /\ ((euclidean__axioms.EF b d l c L C B D) /\ ((euclidean__axioms.EF b d l c C L D B) /\ ((euclidean__axioms.EF b d l c B D L C) /\ ((euclidean__axioms.EF b d l c L D B C) /\ ((euclidean__axioms.EF b d l c C B D L) /\ (euclidean__axioms.EF b d l c D L C B))))))) as H94.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation b d l c D B C L H93).
--------------------------------------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H101.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B D L C b d l c) as H95.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric b d l c B D L C H94).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E C L l e c) as H96.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET E C L c l e) /\ ((euclidean__axioms.ET E C L e l c) /\ ((euclidean__axioms.ET E C L c e l) /\ ((euclidean__axioms.ET E C L l c e) /\ (euclidean__axioms.ET E C L l e c))))) as H96.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation E C L e c l H50).
----------------------------------------------------------------------------- destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H104.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET l e c E C L) as H97.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric E C L l e c H96).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET l e c L E C) as H98.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.ET l e c C L E) /\ ((euclidean__axioms.ET l e c E L C) /\ ((euclidean__axioms.ET l e c C E L) /\ ((euclidean__axioms.ET l e c L C E) /\ (euclidean__axioms.ET l e c L E C))))) as H98.
------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation l e c E C L H97).
------------------------------------------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H106.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET L E C l e c) as H99.
------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric l e c L E C H98).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D L E) as H100.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E L D H3).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS d l e) as H101.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry e l d H4).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C L E) as H102.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C B E L) /\ ((euclidean__defs.Par B C L E) /\ (euclidean__defs.Par C B L E))) as H102.
----------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip B C E L H60).
----------------------------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H105.
---------------------------------------------------------------------------------- assert (euclidean__axioms.Col E L D) as H103 by exact H61.
assert (* Cut *) (euclidean__axioms.Col L E D) as H104.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col E D L) /\ (euclidean__axioms.Col D L E))))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E L D H103).
------------------------------------------------------------------------------------ destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H105.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H105.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq L D) /\ ((euclidean__axioms.neq E L) /\ (euclidean__axioms.neq E D))) as H105.
------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E L D H3).
------------------------------------------------------------------------------------- destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
exact H109.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D E) as H106.
------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E D H105).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C D E) as H107.
-------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel B C D L E H102 H104 H106).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M L C E) as H108.
--------------------------------------------------------------------------------------- destruct H8 as [H108 H109].
destruct H7 as [H110 H111].
exact H111.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E M L) as H109.
---------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric M L C E H108).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP C E M L) as H110.
----------------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B C E M L H109).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS M L C E) as H111.
------------------------------------------------------------------------------------------ destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H116.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS L M C E) as H112.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS L M C E) /\ ((euclidean__defs.OS M L E C) /\ (euclidean__defs.OS L M E C))) as H112.
-------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C E M L H111).
-------------------------------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H113.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M C) as H113.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq l e) /\ ((euclidean__axioms.neq d l) /\ (euclidean__axioms.neq d e))) as H113.
--------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal d l e H101).
--------------------------------------------------------------------------------------------- destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
exact H66.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C M) as H114.
--------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M C H113).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C M B) as H115.
---------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B M C H1).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C M B) as H116.
----------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C M B).
------------------------------------------------------------------------------------------------right.
right.
exact H115.

------------------------------------------------------------------------------------------------ exact H114.
----------------------------------------------------------------------------------------------- assert (* Cut *) (C = C) as H117.
------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point C).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C C E) as H118.
------------------------------------------------------------------------------------------------- left.
exact H117.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS L B C E) as H119.
-------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 C C E L M B H112 H118 H116).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS B L C E) as H120.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS B L C E) /\ ((euclidean__defs.OS L B E C) /\ (euclidean__defs.OS B L E C))) as H120.
---------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C E L B H119).
---------------------------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
exact H121.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E L) as H121.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H121.
----------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M B H115).
----------------------------------------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H65.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E L D) as H122.
----------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 E L D).
------------------------------------------------------------------------------------------------------right.
right.
exact H3.

------------------------------------------------------------------------------------------------------ exact H121.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (E = E) as H123.
------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point E).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C E E) as H124.
------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H123.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS B D C E) as H125.
-------------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 C E E B L D H120 H124 H122).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS D B C E) as H126.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS D B C E) /\ ((euclidean__defs.OS B D E C) /\ (euclidean__defs.OS D B E C))) as H126.
---------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C E B D H125).
---------------------------------------------------------------------------------------------------------- destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
exact H127.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.CR B D C E)) as H127.
---------------------------------------------------------------------------------------------------------- intro H127.
assert (* Cut *) (~(euclidean__axioms.Col B C E)) as H128.
----------------------------------------------------------------------------------------------------------- intro H128.
assert (E = E) as H129 by exact H123.
assert (* Cut *) (euclidean__axioms.Col D E E) as H130.
------------------------------------------------------------------------------------------------------------ right.
right.
left.
exact H129.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet B C D E) as H131.
------------------------------------------------------------------------------------------------------------- exists E.
split.
-------------------------------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet B C D E)) as H132.
-------------------------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H132 by exact H109.
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H132.
destruct __TmpHyp as [x H133].
destruct H133 as [x0 H134].
destruct H134 as [x1 H135].
destruct H135 as [x2 H136].
destruct H136 as [x3 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
assert (exists U V u v X, (euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col M L U) /\ ((euclidean__axioms.Col M L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M L C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H158 by exact H108.
assert (exists U V u v X, (euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col M L U) /\ ((euclidean__axioms.Col M L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M L C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H158.
destruct __TmpHyp0 as [x4 H159].
destruct H159 as [x5 H160].
destruct H160 as [x6 H161].
destruct H161 as [x7 H162].
destruct H162 as [x8 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D E u) /\ ((euclidean__axioms.Col D E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H184 by exact H107.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D E u) /\ ((euclidean__axioms.Col D E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H184.
destruct __TmpHyp1 as [x9 H185].
destruct H185 as [x10 H186].
destruct H186 as [x11 H187].
destruct H187 as [x12 H188].
destruct H188 as [x13 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L E u) /\ ((euclidean__axioms.Col L E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C L E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H210 by exact H102.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L E u) /\ ((euclidean__axioms.Col L E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C L E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H210.
destruct __TmpHyp2 as [x14 H211].
destruct H211 as [x15 H212].
destruct H212 as [x16 H213].
destruct H213 as [x17 H214].
destruct H214 as [x18 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H236 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H236.
destruct __TmpHyp3 as [x19 H237].
destruct H237 as [x20 H238].
destruct H238 as [x21 H239].
destruct H239 as [x22 H240].
destruct H240 as [x23 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
destruct H249 as [H250 H251].
destruct H251 as [H252 H253].
destruct H253 as [H254 H255].
destruct H255 as [H256 H257].
destruct H257 as [H258 H259].
destruct H259 as [H260 H261].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H262 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H262.
destruct __TmpHyp4 as [x24 H263].
destruct H263 as [x25 H264].
destruct H264 as [x26 H265].
destruct H265 as [x27 H266].
destruct H266 as [x28 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
destruct H277 as [H278 H279].
destruct H279 as [H280 H281].
destruct H281 as [H282 H283].
destruct H283 as [H284 H285].
destruct H285 as [H286 H287].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H288 by exact H77.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H288.
destruct __TmpHyp5 as [x29 H289].
destruct H289 as [x30 H290].
destruct H290 as [x31 H291].
destruct H291 as [x32 H292].
destruct H292 as [x33 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
destruct H303 as [H304 H305].
destruct H305 as [H306 H307].
destruct H307 as [H308 H309].
destruct H309 as [H310 H311].
destruct H311 as [H312 H313].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H314 by exact H76.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H314.
destruct __TmpHyp6 as [x34 H315].
destruct H315 as [x35 H316].
destruct H316 as [x36 H317].
destruct H317 as [x37 H318].
destruct H318 as [x38 H319].
destruct H319 as [H320 H321].
destruct H321 as [H322 H323].
destruct H323 as [H324 H325].
destruct H325 as [H326 H327].
destruct H327 as [H328 H329].
destruct H329 as [H330 H331].
destruct H331 as [H332 H333].
destruct H333 as [H334 H335].
destruct H335 as [H336 H337].
destruct H337 as [H338 H339].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H340 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H340.
destruct __TmpHyp7 as [x39 H341].
destruct H341 as [x40 H342].
destruct H342 as [x41 H343].
destruct H343 as [x42 H344].
destruct H344 as [x43 H345].
destruct H345 as [H346 H347].
destruct H347 as [H348 H349].
destruct H349 as [H350 H351].
destruct H351 as [H352 H353].
destruct H353 as [H354 H355].
destruct H355 as [H356 H357].
destruct H357 as [H358 H359].
destruct H359 as [H360 H361].
destruct H361 as [H362 H363].
destruct H363 as [H364 H365].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H366 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H366.
destruct __TmpHyp8 as [x44 H367].
destruct H367 as [x45 H368].
destruct H368 as [x46 H369].
destruct H369 as [x47 H370].
destruct H370 as [x48 H371].
destruct H371 as [H372 H373].
destruct H373 as [H374 H375].
destruct H375 as [H376 H377].
destruct H377 as [H378 H379].
destruct H379 as [H380 H381].
destruct H381 as [H382 H383].
destruct H383 as [H384 H385].
destruct H385 as [H386 H387].
destruct H387 as [H388 H389].
destruct H389 as [H390 H391].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H392 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H392.
destruct __TmpHyp9 as [x49 H393].
destruct H393 as [x50 H394].
destruct H394 as [x51 H395].
destruct H395 as [x52 H396].
destruct H396 as [x53 H397].
destruct H397 as [H398 H399].
destruct H399 as [H400 H401].
destruct H401 as [H402 H403].
destruct H403 as [H404 H405].
destruct H405 as [H406 H407].
destruct H407 as [H408 H409].
destruct H409 as [H410 H411].
destruct H411 as [H412 H413].
destruct H413 as [H414 H415].
destruct H415 as [H416 H417].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H418 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H418.
destruct __TmpHyp10 as [x54 H419].
destruct H419 as [x55 H420].
destruct H420 as [x56 H421].
destruct H421 as [x57 H422].
destruct H422 as [x58 H423].
destruct H423 as [H424 H425].
destruct H425 as [H426 H427].
destruct H427 as [H428 H429].
destruct H429 as [H430 H431].
destruct H431 as [H432 H433].
destruct H433 as [H434 H435].
destruct H435 as [H436 H437].
destruct H437 as [H438 H439].
destruct H439 as [H440 H441].
destruct H441 as [H442 H443].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H444 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H444.
destruct __TmpHyp11 as [x59 H445].
destruct H445 as [x60 H446].
destruct H446 as [x61 H447].
destruct H447 as [x62 H448].
destruct H448 as [x63 H449].
destruct H449 as [H450 H451].
destruct H451 as [H452 H453].
destruct H453 as [H454 H455].
destruct H455 as [H456 H457].
destruct H457 as [H458 H459].
destruct H459 as [H460 H461].
destruct H461 as [H462 H463].
destruct H463 as [H464 H465].
destruct H465 as [H466 H467].
destruct H467 as [H468 H469].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H470 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H470.
destruct __TmpHyp12 as [x64 H471].
destruct H471 as [x65 H472].
destruct H472 as [x66 H473].
destruct H473 as [x67 H474].
destruct H474 as [x68 H475].
destruct H475 as [H476 H477].
destruct H477 as [H478 H479].
destruct H479 as [H480 H481].
destruct H481 as [H482 H483].
destruct H483 as [H484 H485].
destruct H485 as [H486 H487].
destruct H487 as [H488 H489].
destruct H489 as [H490 H491].
destruct H491 as [H492 H493].
destruct H493 as [H494 H495].
exact H206.
-------------------------------------------------------------------------------------------------------------- apply (@H132 H131).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B C E D) as H129.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR B D C E) -> ((euclidean__axioms.nCol B C E) -> (euclidean__axioms.TS B C E D))) as H129.
------------------------------------------------------------------------------------------------------------- intro __.
intro __0.
assert (* AndElim *) ((euclidean__axioms.TS B C E D) /\ ((euclidean__axioms.TS B E C D) /\ ((euclidean__axioms.TS D C E B) /\ (euclidean__axioms.TS D E C B)))) as __1.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite B D C E __ __0).
-------------------------------------------------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
------------------------------------------------------------------------------------------------------------- apply (@H129 H127).
--------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol B C E H128).

------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.TS B C E D)) as H130.
------------------------------------------------------------------------------------------------------------- apply (@lemma__samenotopposite.lemma__samenotopposite B D C E H125).
------------------------------------------------------------------------------------------------------------- apply (@H128).
--------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col B C E).
---------------------------------------------------------------------------------------------------------------intro H131.
apply (@H130 H129).


---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR B E D C) as H128.
----------------------------------------------------------------------------------------------------------- apply (@lemma__crisscross.lemma__crisscross B D C E H107 H127).
----------------------------------------------------------------------------------------------------------- assert (exists T, (euclidean__axioms.BetS B T E) /\ (euclidean__axioms.BetS D T C)) as H129 by exact H128.
destruct H129 as [T H130].
destruct H130 as [H131 H132].
assert (* Cut *) (euclidean__defs.Par b c l e) as H133.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par c b e l) /\ ((euclidean__defs.Par b c l e) /\ (euclidean__defs.Par c b l e))) as H133.
------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip b c e l H78).
------------------------------------------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H136.
------------------------------------------------------------------------------------------------------------ assert (euclidean__axioms.Col e l d) as H134 by exact H79.
assert (* Cut *) (euclidean__axioms.Col l e d) as H135.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col l e d) /\ ((euclidean__axioms.Col l d e) /\ ((euclidean__axioms.Col d e l) /\ ((euclidean__axioms.Col e d l) /\ (euclidean__axioms.Col d l e))))) as H135.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder e l d H134).
-------------------------------------------------------------------------------------------------------------- destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H136.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e d) as H136.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq l d) /\ ((euclidean__axioms.neq e l) /\ (euclidean__axioms.neq e d))) as H136.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal e l d H4).
--------------------------------------------------------------------------------------------------------------- destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
exact H140.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq d e) as H137.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric e d H136).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par b c d e) as H138.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel b c d l e H133 H135 H137).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par m l c e) as H139.
----------------------------------------------------------------------------------------------------------------- destruct H8 as [H139 H140].
destruct H7 as [H141 H142].
exact H140.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par c e m l) as H140.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric m l c e H139).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.TP c e m l) as H141.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B c e m l H140).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS m l c e) as H142.
-------------------------------------------------------------------------------------------------------------------- destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H110 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
exact H147.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS l m c e) as H143.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS l m c e) /\ ((euclidean__defs.OS m l e c) /\ (euclidean__defs.OS l m e c))) as H143.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric c e m l H142).
---------------------------------------------------------------------------------------------------------------------- destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H144.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m c) as H144.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq T C) /\ ((euclidean__axioms.neq D T) /\ (euclidean__axioms.neq D C))) as H144.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D T C H132).
----------------------------------------------------------------------------------------------------------------------- destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H84.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq c m) as H145.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric m c H144).
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS c m b) as H146.
------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry b m c H2).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out c m b) as H147.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 c m b).
--------------------------------------------------------------------------------------------------------------------------right.
right.
exact H146.

-------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (c = c) as H148.
-------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point c).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c c e) as H149.
--------------------------------------------------------------------------------------------------------------------------- left.
exact H148.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS l b c e) as H150.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 c c e l m b H143 H149 H147).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS b l c e) as H151.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS b l c e) /\ ((euclidean__defs.OS l b e c) /\ (euclidean__defs.OS b l e c))) as H151.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric c e l b H150).
------------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
exact H152.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e l) as H152.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m b) /\ ((euclidean__axioms.neq c m) /\ (euclidean__axioms.neq c b))) as H152.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c m b H146).
------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
exact H83.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out e l d) as H153.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 e l d).
--------------------------------------------------------------------------------------------------------------------------------right.
right.
exact H4.

-------------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (e = e) as H154.
-------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point e).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c e e) as H155.
--------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H154.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS b d c e) as H156.
---------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 c e e b l d H151 H155 H153).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS d b c e) as H157.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS d b c e) /\ ((euclidean__defs.OS b d e c) /\ (euclidean__defs.OS d b e c))) as H157.
------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric c e b d H156).
------------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
exact H158.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.CR b d c e)) as H158.
------------------------------------------------------------------------------------------------------------------------------------ intro H158.
assert (* Cut *) (~(euclidean__axioms.Col b c e)) as H159.
------------------------------------------------------------------------------------------------------------------------------------- intro H159.
assert (e = e) as H160 by exact H154.
assert (* Cut *) (euclidean__axioms.Col d e e) as H161.
-------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H160.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet b c d e) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exists e.
split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------- exact H137.
----------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------ exact H161.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet b c d e)) as H163.
---------------------------------------------------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq c e) /\ ((euclidean__axioms.neq m l) /\ ((euclidean__axioms.Col c e U) /\ ((euclidean__axioms.Col c e V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m l u) /\ ((euclidean__axioms.Col m l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet c e m l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H163 by exact H140.
assert (exists U V u v X, (euclidean__axioms.neq c e) /\ ((euclidean__axioms.neq m l) /\ ((euclidean__axioms.Col c e U) /\ ((euclidean__axioms.Col c e V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m l u) /\ ((euclidean__axioms.Col m l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet c e m l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H163.
destruct __TmpHyp as [x H164].
destruct H164 as [x0 H165].
destruct H165 as [x1 H166].
destruct H166 as [x2 H167].
destruct H167 as [x3 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
assert (exists U V u v X, (euclidean__axioms.neq m l) /\ ((euclidean__axioms.neq c e) /\ ((euclidean__axioms.Col m l U) /\ ((euclidean__axioms.Col m l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c e u) /\ ((euclidean__axioms.Col c e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m l c e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H189 by exact H139.
assert (exists U V u v X, (euclidean__axioms.neq m l) /\ ((euclidean__axioms.neq c e) /\ ((euclidean__axioms.Col m l U) /\ ((euclidean__axioms.Col m l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c e u) /\ ((euclidean__axioms.Col c e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m l c e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H189.
destruct __TmpHyp0 as [x4 H190].
destruct H190 as [x5 H191].
destruct H191 as [x6 H192].
destruct H192 as [x7 H193].
destruct H193 as [x8 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d e) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d e u) /\ ((euclidean__axioms.Col d e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H215 by exact H138.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d e) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d e u) /\ ((euclidean__axioms.Col d e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H215.
destruct __TmpHyp1 as [x9 H216].
destruct H216 as [x10 H217].
destruct H217 as [x11 H218].
destruct H218 as [x12 H219].
destruct H219 as [x13 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq l e) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col l e u) /\ ((euclidean__axioms.Col l e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c l e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H241 by exact H133.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq l e) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col l e u) /\ ((euclidean__axioms.Col l e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c l e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H241.
destruct __TmpHyp2 as [x14 H242].
destruct H242 as [x15 H243].
destruct H243 as [x16 H244].
destruct H244 as [x17 H245].
destruct H245 as [x18 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
destruct H264 as [H265 H266].
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H267 by exact H109.
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H267.
destruct __TmpHyp3 as [x19 H268].
destruct H268 as [x20 H269].
destruct H269 as [x21 H270].
destruct H270 as [x22 H271].
destruct H271 as [x23 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
destruct H290 as [H291 H292].
assert (exists U V u v X, (euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col M L U) /\ ((euclidean__axioms.Col M L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M L C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H293 by exact H108.
assert (exists U V u v X, (euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col M L U) /\ ((euclidean__axioms.Col M L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M L C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H293.
destruct __TmpHyp4 as [x24 H294].
destruct H294 as [x25 H295].
destruct H295 as [x26 H296].
destruct H296 as [x27 H297].
destruct H297 as [x28 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
destruct H314 as [H315 H316].
destruct H316 as [H317 H318].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D E u) /\ ((euclidean__axioms.Col D E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H319 by exact H107.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D E u) /\ ((euclidean__axioms.Col D E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H319.
destruct __TmpHyp5 as [x29 H320].
destruct H320 as [x30 H321].
destruct H321 as [x31 H322].
destruct H322 as [x32 H323].
destruct H323 as [x33 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
destruct H336 as [H337 H338].
destruct H338 as [H339 H340].
destruct H340 as [H341 H342].
destruct H342 as [H343 H344].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L E u) /\ ((euclidean__axioms.Col L E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C L E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H345 by exact H102.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L E u) /\ ((euclidean__axioms.Col L E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C L E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H345.
destruct __TmpHyp6 as [x34 H346].
destruct H346 as [x35 H347].
destruct H347 as [x36 H348].
destruct H348 as [x37 H349].
destruct H349 as [x38 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
destruct H360 as [H361 H362].
destruct H362 as [H363 H364].
destruct H364 as [H365 H366].
destruct H366 as [H367 H368].
destruct H368 as [H369 H370].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H371 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq d l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col d l u) /\ ((euclidean__axioms.Col d l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c d l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H371.
destruct __TmpHyp7 as [x39 H372].
destruct H372 as [x40 H373].
destruct H373 as [x41 H374].
destruct H374 as [x42 H375].
destruct H375 as [x43 H376].
destruct H376 as [H377 H378].
destruct H378 as [H379 H380].
destruct H380 as [H381 H382].
destruct H382 as [H383 H384].
destruct H384 as [H385 H386].
destruct H386 as [H387 H388].
destruct H388 as [H389 H390].
destruct H390 as [H391 H392].
destruct H392 as [H393 H394].
destruct H394 as [H395 H396].
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H397 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col b c U) /\ ((euclidean__axioms.Col b c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet b c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H397.
destruct __TmpHyp8 as [x44 H398].
destruct H398 as [x45 H399].
destruct H399 as [x46 H400].
destruct H400 as [x47 H401].
destruct H401 as [x48 H402].
destruct H402 as [H403 H404].
destruct H404 as [H405 H406].
destruct H406 as [H407 H408].
destruct H408 as [H409 H410].
destruct H410 as [H411 H412].
destruct H412 as [H413 H414].
destruct H414 as [H415 H416].
destruct H416 as [H417 H418].
destruct H418 as [H419 H420].
destruct H420 as [H421 H422].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H423 by exact H77.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col b c u) /\ ((euclidean__axioms.Col b c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l b c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H423.
destruct __TmpHyp9 as [x49 H424].
destruct H424 as [x50 H425].
destruct H425 as [x51 H426].
destruct H426 as [x52 H427].
destruct H427 as [x53 H428].
destruct H428 as [H429 H430].
destruct H430 as [H431 H432].
destruct H432 as [H433 H434].
destruct H434 as [H435 H436].
destruct H436 as [H437 H438].
destruct H438 as [H439 H440].
destruct H440 as [H441 H442].
destruct H442 as [H443 H444].
destruct H444 as [H445 H446].
destruct H446 as [H447 H448].
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H449 by exact H76.
assert (exists U V u v X, (euclidean__axioms.neq e l) /\ ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.Col e l U) /\ ((euclidean__axioms.Col e l V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col m c u) /\ ((euclidean__axioms.Col m c v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e l m c)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H449.
destruct __TmpHyp10 as [x54 H450].
destruct H450 as [x55 H451].
destruct H451 as [x56 H452].
destruct H452 as [x57 H453].
destruct H453 as [x58 H454].
destruct H454 as [H455 H456].
destruct H456 as [H457 H458].
destruct H458 as [H459 H460].
destruct H460 as [H461 H462].
destruct H462 as [H463 H464].
destruct H464 as [H465 H466].
destruct H466 as [H467 H468].
destruct H468 as [H469 H470].
destruct H470 as [H471 H472].
destruct H472 as [H473 H474].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H475 by exact H64.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D L u) /\ ((euclidean__axioms.Col D L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C D L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H475.
destruct __TmpHyp11 as [x59 H476].
destruct H476 as [x60 H477].
destruct H477 as [x61 H478].
destruct H478 as [x62 H479].
destruct H479 as [x63 H480].
destruct H480 as [H481 H482].
destruct H482 as [H483 H484].
destruct H484 as [H485 H486].
destruct H486 as [H487 H488].
destruct H488 as [H489 H490].
destruct H490 as [H491 H492].
destruct H492 as [H493 H494].
destruct H494 as [H495 H496].
destruct H496 as [H497 H498].
destruct H498 as [H499 H500].
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H501 by exact H60.
assert (exists U V u v X, (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H501.
destruct __TmpHyp12 as [x64 H502].
destruct H502 as [x65 H503].
destruct H503 as [x66 H504].
destruct H504 as [x67 H505].
destruct H505 as [x68 H506].
destruct H506 as [H507 H508].
destruct H508 as [H509 H510].
destruct H510 as [H511 H512].
destruct H512 as [H513 H514].
destruct H514 as [H515 H516].
destruct H516 as [H517 H518].
destruct H518 as [H519 H520].
destruct H520 as [H521 H522].
destruct H522 as [H523 H524].
destruct H524 as [H525 H526].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H527 by exact H59.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp13 by exact H527.
destruct __TmpHyp13 as [x69 H528].
destruct H528 as [x70 H529].
destruct H529 as [x71 H530].
destruct H530 as [x72 H531].
destruct H531 as [x73 H532].
destruct H532 as [H533 H534].
destruct H534 as [H535 H536].
destruct H536 as [H537 H538].
destruct H538 as [H539 H540].
destruct H540 as [H541 H542].
destruct H542 as [H543 H544].
destruct H544 as [H545 H546].
destruct H546 as [H547 H548].
destruct H548 as [H549 H550].
destruct H550 as [H551 H552].
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H553 by exact H58.
assert (exists U V u v X, (euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.Col E L U) /\ ((euclidean__axioms.Col E L V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M C u) /\ ((euclidean__axioms.Col M C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E L M C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp14 by exact H553.
destruct __TmpHyp14 as [x74 H554].
destruct H554 as [x75 H555].
destruct H555 as [x76 H556].
destruct H556 as [x77 H557].
destruct H557 as [x78 H558].
destruct H558 as [H559 H560].
destruct H560 as [H561 H562].
destruct H562 as [H563 H564].
destruct H564 as [H565 H566].
destruct H566 as [H567 H568].
destruct H568 as [H569 H570].
destruct H570 as [H571 H572].
destruct H572 as [H573 H574].
destruct H574 as [H575 H576].
destruct H576 as [H577 H578].
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H579 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq e l) /\ ((euclidean__axioms.Col m c U) /\ ((euclidean__axioms.Col m c V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e l u) /\ ((euclidean__axioms.Col e l v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet m c e l)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp15 by exact H579.
destruct __TmpHyp15 as [x79 H580].
destruct H580 as [x80 H581].
destruct H581 as [x81 H582].
destruct H582 as [x82 H583].
destruct H583 as [x83 H584].
destruct H584 as [H585 H586].
destruct H586 as [H587 H588].
destruct H588 as [H589 H590].
destruct H590 as [H591 H592].
destruct H592 as [H593 H594].
destruct H594 as [H595 H596].
destruct H596 as [H597 H598].
destruct H598 as [H599 H600].
destruct H600 as [H601 H602].
destruct H602 as [H603 H604].
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H605 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.Col M C U) /\ ((euclidean__axioms.Col M C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E L u) /\ ((euclidean__axioms.Col E L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M C E L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp16 by exact H605.
destruct __TmpHyp16 as [x84 H606].
destruct H606 as [x85 H607].
destruct H607 as [x86 H608].
destruct H608 as [x87 H609].
destruct H609 as [x88 H610].
destruct H610 as [H611 H612].
destruct H612 as [H613 H614].
destruct H614 as [H615 H616].
destruct H616 as [H617 H618].
destruct H618 as [H619 H620].
destruct H620 as [H621 H622].
destruct H622 as [H623 H624].
destruct H624 as [H625 H626].
destruct H626 as [H627 H628].
destruct H628 as [H629 H630].
exact H237.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@H163 H162).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS b c e d) as H160.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR b d c e) -> ((euclidean__axioms.nCol b c e) -> (euclidean__axioms.TS b c e d))) as H160.
--------------------------------------------------------------------------------------------------------------------------------------- intro __.
intro __0.
assert (* AndElim *) ((euclidean__axioms.TS b c e d) /\ ((euclidean__axioms.TS b e c d) /\ ((euclidean__axioms.TS d c e b) /\ (euclidean__axioms.TS d e c b)))) as __1.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite b d c e __ __0).
---------------------------------------------------------------------------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@H160 H158).
----------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol b c e H159).

-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.TS b c e d)) as H161.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samenotopposite.lemma__samenotopposite b d c e H156).
--------------------------------------------------------------------------------------------------------------------------------------- apply (@H159).
----------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col b c e).
-----------------------------------------------------------------------------------------------------------------------------------------intro H162.
apply (@H161 H160).


------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CR b e d c) as H159.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crisscross.lemma__crisscross b d c e H138 H158).
------------------------------------------------------------------------------------------------------------------------------------- assert (exists t, (euclidean__axioms.BetS b t e) /\ (euclidean__axioms.BetS d t c)) as H160 by exact H159.
destruct H160 as [t H161].
destruct H161 as [H162 H163].
assert (* Cut *) (euclidean__axioms.EF B D E C b d e c) as H164.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste2 B D L E C T b d l e c t H100 H101 H99 H95 H131 H132 H162 H163).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B D E C b c e d) as H165.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B D E C d e c b) /\ ((euclidean__axioms.EF B D E C c e d b) /\ ((euclidean__axioms.EF B D E C e c b d) /\ ((euclidean__axioms.EF B D E C d b c e) /\ ((euclidean__axioms.EF B D E C c b d e) /\ ((euclidean__axioms.EF B D E C e d b c) /\ (euclidean__axioms.EF B D E C b c e d))))))) as H165.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation B D E C b d e c H164).
---------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
exact H177.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF b c e d B D E C) as H166.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric B D E C b c e d H165).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF b c e d B C E D) as H167.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF b c e d D E C B) /\ ((euclidean__axioms.EF b c e d C E D B) /\ ((euclidean__axioms.EF b c e d E C B D) /\ ((euclidean__axioms.EF b c e d D B C E) /\ ((euclidean__axioms.EF b c e d C B D E) /\ ((euclidean__axioms.EF b c e d E D B C) /\ (euclidean__axioms.EF b c e d B C E D))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation b c e d B D E C H166).
------------------------------------------------------------------------------------------------------------------------------------------ destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
exact H179.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B C E D b c e d) as H168.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFsymmetric b c e d B C E D H167).
------------------------------------------------------------------------------------------------------------------------------------------ exact H168.
Qed.
