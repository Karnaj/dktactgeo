Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__Euclid4.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__crossimpliesopposite.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equaltorightisright.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__parallelNC.
Require Export lemma__ray4.
Require Export lemma__squareparallelogram.
Require Export lemma__squarerectangle.
Require Export lemma__trichotomy1.
Require Export logic.
Require Export proposition__04.
Require Export proposition__34.
Definition proposition__48A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__defs.SQ A B C D) -> ((euclidean__defs.SQ a b c d) -> ((euclidean__axioms.EF A B C D a b c d) -> (euclidean__axioms.Cong A B a b))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro a.
intro b.
intro c.
intro d.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__defs.PG A B C D) as H2.
- apply (@lemma__squareparallelogram.lemma__squareparallelogram (A) (B) (C) (D) H).
- assert (* Cut *) (euclidean__defs.PG a b c d) as H3.
-- apply (@lemma__squareparallelogram.lemma__squareparallelogram (a) (b) (c) (d) H0).
-- assert (* Cut *) (euclidean__axioms.Cong__3 B A D D C B) as H4.
--- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H4.
---- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
----- destruct __0 as [__0 __1].
exact __1.
---- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H5.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------ apply (@H4 (A0) (B0) (C0) (D0) __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H6.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------- apply (@H5 (A0) (B0) (C0) (D0) __).
------- destruct __0 as [__0 __1].
exact __1.
------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H7.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------- apply (@H6 (A0) (B0) (C0) (D0) __).
-------- destruct __0 as [__0 __1].
exact __1.
------- apply (@H7 (A) (D) (B) (C) H2).
--- assert (* Cut *) (euclidean__axioms.Cong__3 b a d d c b) as H5.
---- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H5.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
------ apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H6.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------- apply (@H5 (A0) (B0) (C0) (D0) __).
------- destruct __0 as [__0 __1].
exact __1.
------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H7.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
-------- apply (@H6 (A0) (B0) (C0) (D0) __).
-------- destruct __0 as [__0 __1].
exact __1.
------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H8.
-------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
--------- apply (@H7 (A0) (B0) (C0) (D0) __).
--------- destruct __0 as [__0 __1].
exact __1.
-------- apply (@H8 (a) (d) (b) (c) H3).
---- assert (* Cut *) (euclidean__axioms.ET B A D D C B) as H6.
----- apply (@euclidean__axioms.axiom__congruentequal (B) (A) (D) (D) (C) (B) H4).
----- assert (* Cut *) (euclidean__axioms.ET b a d d c b) as H7.
------ apply (@euclidean__axioms.axiom__congruentequal (b) (a) (d) (d) (c) (b) H5).
------ assert (* Cut *) (euclidean__axioms.ET B A D B D C) as H8.
------- assert (* Cut *) ((euclidean__axioms.ET B A D C B D) /\ ((euclidean__axioms.ET B A D D B C) /\ ((euclidean__axioms.ET B A D C D B) /\ ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C))))) as H8.
-------- apply (@euclidean__axioms.axiom__ETpermutation (B) (A) (D) (D) (C) (B) H6).
-------- assert (* AndElim *) ((euclidean__axioms.ET B A D C B D) /\ ((euclidean__axioms.ET B A D D B C) /\ ((euclidean__axioms.ET B A D C D B) /\ ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.ET B A D D B C) /\ ((euclidean__axioms.ET B A D C D B) /\ ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C)))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.ET B A D C D B) /\ ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
exact H16.
------- assert (* Cut *) (euclidean__axioms.ET B D C B A D) as H9.
-------- apply (@euclidean__axioms.axiom__ETsymmetric (B) (A) (D) (B) (D) (C) H8).
-------- assert (* Cut *) (euclidean__axioms.ET B D C A B D) as H10.
--------- assert (* Cut *) ((euclidean__axioms.ET B D C A D B) /\ ((euclidean__axioms.ET B D C B D A) /\ ((euclidean__axioms.ET B D C A B D) /\ ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A))))) as H10.
---------- apply (@euclidean__axioms.axiom__ETpermutation (B) (D) (C) (B) (A) (D) H9).
---------- assert (* AndElim *) ((euclidean__axioms.ET B D C A D B) /\ ((euclidean__axioms.ET B D C B D A) /\ ((euclidean__axioms.ET B D C A B D) /\ ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.ET B D C B D A) /\ ((euclidean__axioms.ET B D C A B D) /\ ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.ET B D C A B D) /\ ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.ET A B D B D C) as H11.
---------- apply (@euclidean__axioms.axiom__ETsymmetric (B) (D) (C) (A) (B) (D) H10).
---------- assert (* Cut *) (euclidean__axioms.ET b a d b d c) as H12.
----------- assert (* Cut *) ((euclidean__axioms.ET b a d c b d) /\ ((euclidean__axioms.ET b a d d b c) /\ ((euclidean__axioms.ET b a d c d b) /\ ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c))))) as H12.
------------ apply (@euclidean__axioms.axiom__ETpermutation (b) (a) (d) (d) (c) (b) H7).
------------ assert (* AndElim *) ((euclidean__axioms.ET b a d c b d) /\ ((euclidean__axioms.ET b a d d b c) /\ ((euclidean__axioms.ET b a d c d b) /\ ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.ET b a d d b c) /\ ((euclidean__axioms.ET b a d c d b) /\ ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c)))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.ET b a d c d b) /\ ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H20.
----------- assert (* Cut *) (euclidean__axioms.ET b d c b a d) as H13.
------------ apply (@euclidean__axioms.axiom__ETsymmetric (b) (a) (d) (b) (d) (c) H12).
------------ assert (* Cut *) (euclidean__axioms.ET b d c a b d) as H14.
------------- assert (* Cut *) ((euclidean__axioms.ET b d c a d b) /\ ((euclidean__axioms.ET b d c b d a) /\ ((euclidean__axioms.ET b d c a b d) /\ ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a))))) as H14.
-------------- apply (@euclidean__axioms.axiom__ETpermutation (b) (d) (c) (b) (a) (d) H13).
-------------- assert (* AndElim *) ((euclidean__axioms.ET b d c a d b) /\ ((euclidean__axioms.ET b d c b d a) /\ ((euclidean__axioms.ET b d c a b d) /\ ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a))))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.ET b d c b d a) /\ ((euclidean__axioms.ET b d c a b d) /\ ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a)))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.ET b d c a b d) /\ ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a)) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
exact H19.
------------- assert (* Cut *) (euclidean__axioms.ET a b d b d c) as H15.
-------------- apply (@euclidean__axioms.axiom__ETsymmetric (b) (d) (c) (a) (b) (d) H14).
-------------- assert (* Cut *) (euclidean__defs.RE A B C D) as H16.
--------------- apply (@lemma__squarerectangle.lemma__squarerectangle (A) (B) (C) (D) H).
--------------- assert (* Cut *) (euclidean__defs.RE a b c d) as H17.
---------------- apply (@lemma__squarerectangle.lemma__squarerectangle (a) (b) (c) (d) H0).
---------------- assert (* Cut *) (euclidean__defs.CR A C B D) as H18.
----------------- assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H26.
---------------------- exact H16.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
exact H33.
----------------- assert (* Cut *) (euclidean__defs.CR a c b d) as H19.
------------------ assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))))) as H19.
------------------- exact H17.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H27.
----------------------- exact H16.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H26.
------------------ assert (* Cut *) (euclidean__defs.Par A B C D) as H20.
------------------- assert (* AndElim *) ((euclidean__defs.Par a b c d) /\ (euclidean__defs.Par a d b c)) as H20.
-------------------- exact H3.
-------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H22.
--------------------- exact H2.
--------------------- destruct H22 as [H22 H23].
exact H22.
------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H21.
-------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H21.
--------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H20).
--------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H22.
---------------------- exact H21.
---------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H24.
----------------------- exact H23.
----------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
exact H27.
-------------------- assert (* Cut *) (euclidean__defs.Par a b c d) as H22.
--------------------- assert (* AndElim *) ((euclidean__defs.Par a b c d) /\ (euclidean__defs.Par a d b c)) as H22.
---------------------- exact H3.
---------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H24.
----------------------- exact H2.
----------------------- destruct H24 as [H24 H25].
exact H22.
--------------------- assert (* Cut *) (euclidean__axioms.nCol a b d) as H23.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H23.
----------------------- apply (@lemma__parallelNC.lemma__parallelNC (a) (b) (c) (d) H22).
----------------------- assert (* AndElim *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d))) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
exact H29.
---------------------- assert (* Cut *) (euclidean__axioms.TS A B D C) as H24.
----------------------- assert (* Cut *) ((euclidean__axioms.TS A B D C) /\ ((euclidean__axioms.TS A D B C) /\ ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A)))) as H24.
------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite (A) (C) (B) (D) (H18) H21).
------------------------ assert (* AndElim *) ((euclidean__axioms.TS A B D C) /\ ((euclidean__axioms.TS A D B C) /\ ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A)))) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.TS A D B C) /\ ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A)) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
exact H25.
----------------------- assert (* Cut *) (euclidean__axioms.TS a b d c) as H25.
------------------------ assert (* Cut *) ((euclidean__axioms.TS a b d c) /\ ((euclidean__axioms.TS a d b c) /\ ((euclidean__axioms.TS c b d a) /\ (euclidean__axioms.TS c d b a)))) as H25.
------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite (a) (c) (b) (d) (H19) H23).
------------------------- assert (* AndElim *) ((euclidean__axioms.TS a b d c) /\ ((euclidean__axioms.TS a d b c) /\ ((euclidean__axioms.TS c b d a) /\ (euclidean__axioms.TS c d b a)))) as H26.
-------------------------- exact H25.
-------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.TS a d b c) /\ ((euclidean__axioms.TS c b d a) /\ (euclidean__axioms.TS c d b a))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.TS c b d a) /\ (euclidean__axioms.TS c d b a)) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
exact H26.
------------------------ assert (* Cut *) (euclidean__axioms.ET A B D a b d) as H26.
------------------------- apply (@euclidean__axioms.axiom__halvesofequals (A) (B) (D) (C) (a) (b) (d) (c) (H11) (H24) (H15) (H25) H1).
------------------------- assert (* Cut *) (euclidean__axioms.Cong a b d a) as H27.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H27.
--------------------------- exact H0.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H39.
--------------------------------- exact H.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H43.
----------------------------------- exact H42.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H45.
------------------------------------ exact H44.
------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H47.
------------------------------------- exact H46.
------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H49.
-------------------------------------- exact H48.
-------------------------------------- destruct H49 as [H49 H50].
exact H31.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H28.
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H28.
---------------------------- exact H0.
---------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H40.
---------------------------------- exact H.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H46.
------------------------------------- exact H45.
------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H48.
-------------------------------------- exact H47.
-------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H50.
--------------------------------------- exact H49.
--------------------------------------- destruct H50 as [H50 H51].
exact H44.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong a b a d) as H29.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong b a a d) /\ ((euclidean__axioms.Cong b a d a) /\ (euclidean__axioms.Cong a b a d))) as H29.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (a) (b) (d) (a) H27).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong b a a d) /\ ((euclidean__axioms.Cong b a d a) /\ (euclidean__axioms.Cong a b a d))) as H30.
------------------------------ exact H29.
------------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong b a d a) /\ (euclidean__axioms.Cong a b a d)) as H32.
------------------------------- exact H31.
------------------------------- destruct H32 as [H32 H33].
exact H33.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H30.
----------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A A D) /\ ((euclidean__axioms.Cong B A D A) /\ (euclidean__axioms.Cong A B A D))) as H30.
------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (A) H28).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A A D) /\ ((euclidean__axioms.Cong B A D A) /\ (euclidean__axioms.Cong A B A D))) as H31.
------------------------------- exact H30.
------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Cong B A D A) /\ (euclidean__axioms.Cong A B A D)) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
exact H34.
----------------------------- assert (* Cut *) (~(euclidean__defs.Lt a b A B)) as H31.
------------------------------ intro H31.
assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E a b)) as H32.
------------------------------- exact H31.
------------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E a b))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [E H33].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E a b)) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [H34 H35].
assert (* Cut *) (euclidean__defs.Lt a d A B) as H36.
---------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (a) (b) (A) (B) (a) (d) (H31) H29).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt a d A D) as H37.
----------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (a) (d) (A) (B) (A) (D) (H36) H30).
----------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F a d)) as H38.
------------------------------------ exact H37.
------------------------------------ assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F a d))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [F H39].
assert (* AndElim *) ((euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F a d)) as H40.
-------------------------------------- exact H39.
-------------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) (euclidean__defs.Per D A B) as H42.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H42.
---------------------------------------- exact H0.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H54.
---------------------------------------------- exact H.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H58.
------------------------------------------------ exact H57.
------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H60.
------------------------------------------------- exact H59.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H62.
-------------------------------------------------- exact H61.
-------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H64.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H64 as [H64 H65].
exact H60.
--------------------------------------- assert (* Cut *) (euclidean__defs.Per d a b) as H43.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H43.
----------------------------------------- exact H0.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H55.
----------------------------------------------- exact H.
----------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H61.
-------------------------------------------------- exact H60.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H65.
---------------------------------------------------- exact H64.
---------------------------------------------------- destruct H65 as [H65 H66].
exact H49.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H44.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A D))) as H44.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (F) (D) H40).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A D))) as H45.
------------------------------------------- exact H44.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A D)) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
exact H48.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H45.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H45.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H34).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H46.
-------------------------------------------- exact H45.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
exact H49.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out A D F) as H46.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (D) (F)).
--------------------------------------------left.
exact H40.

-------------------------------------------- exact H44.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out A B E) as H47.
-------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (B) (E)).
---------------------------------------------left.
exact H34.

--------------------------------------------- exact H45.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H48.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H48.
---------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (D) H21).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H49.
----------------------------------------------- exact H48.
----------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)))) as H51.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))) as H53.
------------------------------------------------- exact H52.
------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)) as H55.
-------------------------------------------------- exact H54.
-------------------------------------------------- destruct H55 as [H55 H56].
exact H53.
--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B D A B) as H49.
---------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (D) (A) (B) H48).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B F A E) as H50.
----------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (A) (B) (D) (A) (B) (F) (E) (H49) (H46) H47).
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A E D A B) as H51.
------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (A) (B) (F) (A) (E) H50).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Per F A E) as H52.
------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright (D) (A) (B) (F) (A) (E) (H42) H51).
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A E d a b) as H53.
-------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 (F) (A) (E) (d) (a) (b) (H52) H43).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E d b) as H54.
--------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H54.
---------------------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
----------------------------------------------------- apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a0) (b0) (c0) (__) (__0) __1).
----------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
---------------------------------------------------- apply (@H54 (A) (F) (E) (a) (d) (b) (H41) (H35) H53).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F A d a) as H55.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A d a) /\ ((euclidean__axioms.Cong F A a d) /\ (euclidean__axioms.Cong A F d a))) as H55.
----------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (F) (a) (d) H41).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A d a) /\ ((euclidean__axioms.Cong F A a d) /\ (euclidean__axioms.Cong A F d a))) as H56.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong F A a d) /\ (euclidean__axioms.Cong A F d a)) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
exact H56.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 F A E d a b) as H56.
----------------------------------------------------- split.
------------------------------------------------------ exact H55.
------------------------------------------------------ split.
------------------------------------------------------- exact H35.
------------------------------------------------------- exact H54.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E d a b) as H57.
------------------------------------------------------ apply (@euclidean__axioms.axiom__congruentequal (F) (A) (E) (d) (a) (b) H56).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F A E a b d) as H58.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F A E a b d) /\ ((euclidean__axioms.ET F A E d b a) /\ ((euclidean__axioms.ET F A E a d b) /\ ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a))))) as H58.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (A) (E) (d) (a) (b) H57).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F A E a b d) /\ ((euclidean__axioms.ET F A E d b a) /\ ((euclidean__axioms.ET F A E a d b) /\ ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a))))) as H59.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.ET F A E d b a) /\ ((euclidean__axioms.ET F A E a d b) /\ ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a)))) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.ET F A E a d b) /\ ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a))) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a)) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
exact H59.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET a b d A B D) as H59.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (D) (a) (b) (d) H26).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E A B D) as H60.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (F) (A) (E) (A) (B) (D) (a) (b) (d) (H58) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E D A B) as H61.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F A E B D A) /\ ((euclidean__axioms.ET F A E A D B) /\ ((euclidean__axioms.ET F A E B A D) /\ ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B))))) as H61.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (F) (A) (E) (A) (B) (D) H60).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET F A E B D A) /\ ((euclidean__axioms.ET F A E A D B) /\ ((euclidean__axioms.ET F A E B A D) /\ ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B))))) as H62.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.ET F A E A D B) /\ ((euclidean__axioms.ET F A E B A D) /\ ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B)))) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.ET F A E B A D) /\ ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B))) as H66.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B)) as H68.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D A B F A E) as H62.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (F) (A) (E) (D) (A) (B) H61).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle D A B) as H63.
------------------------------------------------------------ exact H48.
------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.ET D A B F A E)) as H64.
------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt2 (D) (A) (B) (F) (E) (H63) (H40) H34).
------------------------------------------------------------- apply (@H64 H62).
------------------------------ assert (* Cut *) (~(euclidean__defs.Lt A B a b)) as H32.
------------------------------- intro H32.
assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS a e b) /\ (euclidean__axioms.Cong a e A B)) as H33.
-------------------------------- exact H32.
-------------------------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS a e b) /\ (euclidean__axioms.Cong a e A B))) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [e H34].
assert (* AndElim *) ((euclidean__axioms.BetS a e b) /\ (euclidean__axioms.Cong a e A B)) as H35.
---------------------------------- exact H34.
---------------------------------- destruct H35 as [H35 H36].
assert (* Cut *) (euclidean__defs.Lt A D a b) as H37.
----------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (A) (B) (a) (b) (A) (D) (H32) H30).
----------------------------------- assert (* Cut *) (euclidean__defs.Lt A D a d) as H38.
------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (D) (a) (b) (a) (d) (H37) H29).
------------------------------------ assert (* Cut *) (exists (f: euclidean__axioms.Point), (euclidean__axioms.BetS a f d) /\ (euclidean__axioms.Cong a f A D)) as H39.
------------------------------------- exact H38.
------------------------------------- assert (exists f: euclidean__axioms.Point, ((euclidean__axioms.BetS a f d) /\ (euclidean__axioms.Cong a f A D))) as H40.
-------------------------------------- exact H39.
-------------------------------------- destruct H40 as [f H40].
assert (* AndElim *) ((euclidean__axioms.BetS a f d) /\ (euclidean__axioms.Cong a f A D)) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
assert (* Cut *) (euclidean__defs.Per d a b) as H43.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H43.
----------------------------------------- exact H0.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H55.
----------------------------------------------- exact H.
----------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H61.
-------------------------------------------------- exact H60.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H65.
---------------------------------------------------- exact H64.
---------------------------------------------------- destruct H65 as [H65 H66].
exact H49.
---------------------------------------- assert (* Cut *) (euclidean__defs.Per D A B) as H44.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H44.
------------------------------------------ exact H0.
------------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H46.
------------------------------------------- exact H45.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H52.
---------------------------------------------- exact H51.
---------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H54.
----------------------------------------------- exact H53.
----------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H56.
------------------------------------------------ exact H.
------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H62.
--------------------------------------------------- exact H61.
--------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H64.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H66.
----------------------------------------------------- exact H65.
----------------------------------------------------- destruct H66 as [H66 H67].
exact H62.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq a d) as H45.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq f d) /\ ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a d))) as H45.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (f) (d) H41).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq f d) /\ ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a d))) as H46.
-------------------------------------------- exact H45.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a d)) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
exact H49.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq a b) as H46.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e b) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a b))) as H46.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (e) (b) H35).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e b) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a b))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a b)) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
exact H50.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out a d f) as H47.
-------------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (d) (f)).
---------------------------------------------left.
exact H41.

--------------------------------------------- exact H45.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Out a b e) as H48.
--------------------------------------------- apply (@lemma__ray4.lemma__ray4 (a) (b) (e)).
----------------------------------------------left.
exact H35.

---------------------------------------------- exact H46.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d a b) as H49.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol b a d) /\ ((euclidean__axioms.nCol b d a) /\ ((euclidean__axioms.nCol d a b) /\ ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a))))) as H49.
----------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (a) (b) (d) H23).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol b a d) /\ ((euclidean__axioms.nCol b d a) /\ ((euclidean__axioms.nCol d a b) /\ ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a))))) as H50.
------------------------------------------------ exact H49.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol b d a) /\ ((euclidean__axioms.nCol d a b) /\ ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a)))) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol d a b) /\ ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a)) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
exact H54.
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA d a b d a b) as H50.
----------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (d) (a) (b) H49).
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA d a b f a e) as H51.
------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (d) (a) (b) (d) (a) (b) (f) (e) (H50) (H47) H48).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA f a e d a b) as H52.
------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (d) (a) (b) (f) (a) (e) H51).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Per f a e) as H53.
-------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright (d) (a) (b) (f) (a) (e) (H43) H52).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA f a e D A B) as H54.
--------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 (f) (a) (e) (D) (A) (B) (H53) H44).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong f e D B) as H55.
---------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H55.
----------------------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
------------------------------------------------------ apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a0) (b0) (c0) (__) (__0) __1).
------------------------------------------------------ destruct __2 as [__2 __3].
exact __2.
----------------------------------------------------- apply (@H55 (a) (f) (e) (A) (D) (B) (H42) (H36) H54).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong f a D A) as H56.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong f a D A) /\ ((euclidean__axioms.Cong f a A D) /\ (euclidean__axioms.Cong a f D A))) as H56.
------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (a) (f) (A) (D) H42).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong f a D A) /\ ((euclidean__axioms.Cong f a A D) /\ (euclidean__axioms.Cong a f D A))) as H57.
------------------------------------------------------- exact H56.
------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Cong f a A D) /\ (euclidean__axioms.Cong a f D A)) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 f a e D A B) as H57.
------------------------------------------------------ split.
------------------------------------------------------- exact H56.
------------------------------------------------------- split.
-------------------------------------------------------- exact H36.
-------------------------------------------------------- exact H55.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET f a e D A B) as H58.
------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (f) (a) (e) (D) (A) (B) H57).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e A B D) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET f a e A B D) /\ ((euclidean__axioms.ET f a e D B A) /\ ((euclidean__axioms.ET f a e A D B) /\ ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A))))) as H59.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (f) (a) (e) (D) (A) (B) H58).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET f a e A B D) /\ ((euclidean__axioms.ET f a e D B A) /\ ((euclidean__axioms.ET f a e A D B) /\ ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A))))) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.ET f a e D B A) /\ ((euclidean__axioms.ET f a e A D B) /\ ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A)))) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.ET f a e A D B) /\ ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A)) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
exact H60.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D f a e) as H60.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (f) (a) (e) (A) (B) (D) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e a b d) as H61.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (f) (a) (e) (a) (b) (d) (A) (B) (D) (H59) H26).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e d a b) as H62.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET f a e b d a) /\ ((euclidean__axioms.ET f a e a d b) /\ ((euclidean__axioms.ET f a e b a d) /\ ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b))))) as H62.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (f) (a) (e) (a) (b) (d) H61).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET f a e b d a) /\ ((euclidean__axioms.ET f a e a d b) /\ ((euclidean__axioms.ET f a e b a d) /\ ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b))))) as H63.
------------------------------------------------------------- exact H62.
------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.ET f a e a d b) /\ ((euclidean__axioms.ET f a e b a d) /\ ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b)))) as H65.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.ET f a e b a d) /\ ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b))) as H67.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b)) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
exact H70.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET d a b f a e) as H63.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (f) (a) (e) (d) (a) (b) H62).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Triangle d a b) as H64.
------------------------------------------------------------- exact H49.
------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.ET d a b f a e)) as H65.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt2 (d) (a) (b) (f) (e) (H64) (H41) H35).
-------------------------------------------------------------- apply (@H65 H63).
------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H33.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H33.
--------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (D) H21).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H34.
---------------------------------- exact H33.
---------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A))))) as H36.
----------------------------------- exact H35.
----------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
exact H34.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq a b) as H34.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b d) /\ ((euclidean__axioms.neq a d) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a)))))) as H34.
---------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (a) (b) (d) H23).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b d) /\ ((euclidean__axioms.neq a d) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a)))))) as H35.
----------------------------------- exact H34.
----------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq b d) /\ ((euclidean__axioms.neq a d) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a))))) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq a d) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a)))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
exact H35.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B a b) as H35.
---------------------------------- apply (@lemma__trichotomy1.lemma__trichotomy1 (A) (B) (a) (b) (H32) (H31) (H33) H34).
---------------------------------- exact H35.
Qed.
