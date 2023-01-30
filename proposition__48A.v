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
Definition proposition__48A : forall A B C D a b c d, (euclidean__defs.SQ A B C D) -> ((euclidean__defs.SQ a b c d) -> ((euclidean__axioms.EF A B C D a b c d) -> (euclidean__axioms.Cong A B a b))).
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
- apply (@lemma__squareparallelogram.lemma__squareparallelogram A B C D H).
- assert (* Cut *) (euclidean__defs.PG a b c d) as H3.
-- apply (@lemma__squareparallelogram.lemma__squareparallelogram a b c d H0).
-- assert (* Cut *) (euclidean__axioms.Cong__3 B A D D C B) as H4.
--- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H4.
---- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
----- destruct __0 as [__0 __1].
exact __1.
---- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H5.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------ apply (@H4 A0 B0 C0 D0 __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H6.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------- apply (@H5 A0 B0 C0 D0 __).
------- destruct __0 as [__0 __1].
exact __1.
------ assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H7.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------- apply (@H6 A0 B0 C0 D0 __).
-------- destruct __0 as [__0 __1].
exact __1.
------- apply (@H7 A D B C H2).
--- assert (* Cut *) (euclidean__axioms.Cong__3 b a d d c b) as H5.
---- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H5.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
------ apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H6.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------- apply (@H5 A0 B0 C0 D0 __).
------- destruct __0 as [__0 __1].
exact __1.
------ assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H7.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
-------- apply (@H6 A0 B0 C0 D0 __).
-------- destruct __0 as [__0 __1].
exact __1.
------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H8.
-------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
--------- apply (@H7 A0 B0 C0 D0 __).
--------- destruct __0 as [__0 __1].
exact __1.
-------- apply (@H8 a d b c H3).
---- assert (* Cut *) (euclidean__axioms.ET B A D D C B) as H6.
----- apply (@euclidean__axioms.axiom__congruentequal B A D D C B H4).
----- assert (* Cut *) (euclidean__axioms.ET b a d d c b) as H7.
------ apply (@euclidean__axioms.axiom__congruentequal b a d d c b H5).
------ assert (* Cut *) (euclidean__axioms.ET B A D B D C) as H8.
------- assert (* Cut *) ((euclidean__axioms.ET B A D C B D) /\ ((euclidean__axioms.ET B A D D B C) /\ ((euclidean__axioms.ET B A D C D B) /\ ((euclidean__axioms.ET B A D B C D) /\ (euclidean__axioms.ET B A D B D C))))) as H8.
-------- apply (@euclidean__axioms.axiom__ETpermutation B A D D C B H6).
-------- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H16.
------- assert (* Cut *) (euclidean__axioms.ET B D C B A D) as H9.
-------- apply (@euclidean__axioms.axiom__ETsymmetric B A D B D C H8).
-------- assert (* Cut *) (euclidean__axioms.ET B D C A B D) as H10.
--------- assert (* Cut *) ((euclidean__axioms.ET B D C A D B) /\ ((euclidean__axioms.ET B D C B D A) /\ ((euclidean__axioms.ET B D C A B D) /\ ((euclidean__axioms.ET B D C D A B) /\ (euclidean__axioms.ET B D C D B A))))) as H10.
---------- apply (@euclidean__axioms.axiom__ETpermutation B D C B A D H9).
---------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.ET A B D B D C) as H11.
---------- apply (@euclidean__axioms.axiom__ETsymmetric B D C A B D H10).
---------- assert (* Cut *) (euclidean__axioms.ET b a d b d c) as H12.
----------- assert (* Cut *) ((euclidean__axioms.ET b a d c b d) /\ ((euclidean__axioms.ET b a d d b c) /\ ((euclidean__axioms.ET b a d c d b) /\ ((euclidean__axioms.ET b a d b c d) /\ (euclidean__axioms.ET b a d b d c))))) as H12.
------------ apply (@euclidean__axioms.axiom__ETpermutation b a d d c b H7).
------------ destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
----------- assert (* Cut *) (euclidean__axioms.ET b d c b a d) as H13.
------------ apply (@euclidean__axioms.axiom__ETsymmetric b a d b d c H12).
------------ assert (* Cut *) (euclidean__axioms.ET b d c a b d) as H14.
------------- assert (* Cut *) ((euclidean__axioms.ET b d c a d b) /\ ((euclidean__axioms.ET b d c b d a) /\ ((euclidean__axioms.ET b d c a b d) /\ ((euclidean__axioms.ET b d c d a b) /\ (euclidean__axioms.ET b d c d b a))))) as H14.
-------------- apply (@euclidean__axioms.axiom__ETpermutation b d c b a d H13).
-------------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H19.
------------- assert (* Cut *) (euclidean__axioms.ET a b d b d c) as H15.
-------------- apply (@euclidean__axioms.axiom__ETsymmetric b d c a b d H14).
-------------- assert (* Cut *) (euclidean__defs.RE A B C D) as H16.
--------------- apply (@lemma__squarerectangle.lemma__squarerectangle A B C D H).
--------------- assert (* Cut *) (euclidean__defs.RE a b c d) as H17.
---------------- apply (@lemma__squarerectangle.lemma__squarerectangle a b c d H0).
---------------- assert (* Cut *) (euclidean__defs.CR A C B D) as H18.
----------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H16 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H33.
----------------- assert (* Cut *) (euclidean__defs.CR a c b d) as H19.
------------------ destruct H17 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H16 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H26.
------------------ assert (* Cut *) (euclidean__defs.Par A B C D) as H20.
------------------- destruct H3 as [H20 H21].
destruct H2 as [H22 H23].
exact H22.
------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H21.
-------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H21.
--------------------- apply (@lemma__parallelNC.lemma__parallelNC A B C D H20).
--------------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H27.
-------------------- assert (* Cut *) (euclidean__defs.Par a b c d) as H22.
--------------------- destruct H3 as [H22 H23].
destruct H2 as [H24 H25].
exact H22.
--------------------- assert (* Cut *) (euclidean__axioms.nCol a b d) as H23.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H23.
----------------------- apply (@lemma__parallelNC.lemma__parallelNC a b c d H22).
----------------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H29.
---------------------- assert (* Cut *) (euclidean__axioms.TS A B D C) as H24.
----------------------- assert (* Cut *) ((euclidean__axioms.TS A B D C) /\ ((euclidean__axioms.TS A D B C) /\ ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A)))) as H24.
------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite A C B D H18 H21).
------------------------ destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H25.
----------------------- assert (* Cut *) (euclidean__axioms.TS a b d c) as H25.
------------------------ assert (* Cut *) ((euclidean__axioms.TS a b d c) /\ ((euclidean__axioms.TS a d b c) /\ ((euclidean__axioms.TS c b d a) /\ (euclidean__axioms.TS c d b a)))) as H25.
------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite a c b d H19 H23).
------------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H26.
------------------------ assert (* Cut *) (euclidean__axioms.ET A B D a b d) as H26.
------------------------- apply (@euclidean__axioms.axiom__halvesofequals A B D C a b d c H11 H24 H15 H25 H1).
------------------------- assert (* Cut *) (euclidean__axioms.Cong a b d a) as H27.
-------------------------- destruct H0 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H31.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H28.
--------------------------- destruct H0 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H44.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong a b a d) as H29.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong b a a d) /\ ((euclidean__axioms.Cong b a d a) /\ (euclidean__axioms.Cong a b a d))) as H29.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip a b d a H27).
----------------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H33.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H30.
----------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A A D) /\ ((euclidean__axioms.Cong B A D A) /\ (euclidean__axioms.Cong A B A D))) as H30.
------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A B D A H28).
------------------------------ destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H34.
----------------------------- assert (* Cut *) (~(euclidean__defs.Lt a b A B)) as H31.
------------------------------ intro H31.
assert (exists E, (euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E a b)) as H32 by exact H31.
destruct H32 as [E H33].
destruct H33 as [H34 H35].
assert (* Cut *) (euclidean__defs.Lt a d A B) as H36.
------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 a b A B a d H31 H29).
------------------------------- assert (* Cut *) (euclidean__defs.Lt a d A D) as H37.
-------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence a d A B A D H36 H30).
-------------------------------- assert (exists F, (euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F a d)) as H38 by exact H37.
destruct H38 as [F H39].
destruct H39 as [H40 H41].
assert (* Cut *) (euclidean__defs.Per D A B) as H42.
--------------------------------- destruct H0 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H60.
--------------------------------- assert (* Cut *) (euclidean__defs.Per d a b) as H43.
---------------------------------- destruct H0 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H49.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H44.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A D))) as H44.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A F D H40).
------------------------------------ destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H48.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H45.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H45.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A E B H34).
------------------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
------------------------------------ assert (* Cut *) (euclidean__defs.Out A D F) as H46.
------------------------------------- apply (@lemma__ray4.lemma__ray4 A D F).
--------------------------------------left.
exact H40.

-------------------------------------- exact H44.
------------------------------------- assert (* Cut *) (euclidean__defs.Out A B E) as H47.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 A B E).
---------------------------------------left.
exact H34.

--------------------------------------- exact H45.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H48.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H48.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder A B D H21).
---------------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B D A B) as H49.
---------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive D A B H48).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A B F A E) as H50.
----------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper D A B D A B F E H49 H46 H47).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A E D A B) as H51.
------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D A B F A E H50).
------------------------------------------ assert (* Cut *) (euclidean__defs.Per F A E) as H52.
------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright D A B F A E H42 H51).
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A E d a b) as H53.
-------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 F A E d a b H52 H43).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E d b) as H54.
--------------------------------------------- assert (* Cut *) (forall A0 B0 C0 a0 b0 c0, (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H54.
---------------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
----------------------------------------------- apply (@proposition__04.proposition__04 A0 B0 C0 a0 b0 c0 __ __0 __1).
----------------------------------------------- destruct __2 as [__2 __3].
exact __2.
---------------------------------------------- apply (@H54 A F E a d b H41 H35 H53).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F A d a) as H55.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A d a) /\ ((euclidean__axioms.Cong F A a d) /\ (euclidean__axioms.Cong A F d a))) as H55.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A F a d H41).
----------------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H56.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 F A E d a b) as H56.
----------------------------------------------- split.
------------------------------------------------ exact H55.
------------------------------------------------ split.
------------------------------------------------- exact H35.
------------------------------------------------- exact H54.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E d a b) as H57.
------------------------------------------------ apply (@euclidean__axioms.axiom__congruentequal F A E d a b H56).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F A E a b d) as H58.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F A E a b d) /\ ((euclidean__axioms.ET F A E d b a) /\ ((euclidean__axioms.ET F A E a d b) /\ ((euclidean__axioms.ET F A E b a d) /\ (euclidean__axioms.ET F A E b d a))))) as H58.
-------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F A E d a b H57).
-------------------------------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H59.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET a b d A B D) as H59.
-------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric A B D a b d H26).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E A B D) as H60.
--------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive F A E A B D a b d H58 H59).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A E D A B) as H61.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F A E B D A) /\ ((euclidean__axioms.ET F A E A D B) /\ ((euclidean__axioms.ET F A E B A D) /\ ((euclidean__axioms.ET F A E D B A) /\ (euclidean__axioms.ET F A E D A B))))) as H61.
----------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F A E A B D H60).
----------------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H69.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D A B F A E) as H62.
----------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric F A E D A B H61).
----------------------------------------------------- assert (euclidean__axioms.Triangle D A B) as H63 by exact H48.
assert (* Cut *) (~(euclidean__axioms.ET D A B F A E)) as H64.
------------------------------------------------------ apply (@euclidean__axioms.axiom__deZolt2 D A B F E H63 H40 H34).
------------------------------------------------------ apply (@H64 H62).
------------------------------ assert (* Cut *) (~(euclidean__defs.Lt A B a b)) as H32.
------------------------------- intro H32.
assert (exists e, (euclidean__axioms.BetS a e b) /\ (euclidean__axioms.Cong a e A B)) as H33 by exact H32.
destruct H33 as [e H34].
destruct H34 as [H35 H36].
assert (* Cut *) (euclidean__defs.Lt A D a b) as H37.
-------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 A B a b A D H32 H30).
-------------------------------- assert (* Cut *) (euclidean__defs.Lt A D a d) as H38.
--------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence A D a b a d H37 H29).
--------------------------------- assert (exists f, (euclidean__axioms.BetS a f d) /\ (euclidean__axioms.Cong a f A D)) as H39 by exact H38.
destruct H39 as [f H40].
destruct H40 as [H41 H42].
assert (* Cut *) (euclidean__defs.Per d a b) as H43.
---------------------------------- destruct H0 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H49.
---------------------------------- assert (* Cut *) (euclidean__defs.Per D A B) as H44.
----------------------------------- destruct H0 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq a d) as H45.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq f d) /\ ((euclidean__axioms.neq a f) /\ (euclidean__axioms.neq a d))) as H45.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal a f d H41).
------------------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq a b) as H46.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e b) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a b))) as H46.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal a e b H35).
-------------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H50.
------------------------------------- assert (* Cut *) (euclidean__defs.Out a d f) as H47.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 a d f).
---------------------------------------left.
exact H41.

--------------------------------------- exact H45.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out a b e) as H48.
--------------------------------------- apply (@lemma__ray4.lemma__ray4 a b e).
----------------------------------------left.
exact H35.

---------------------------------------- exact H46.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d a b) as H49.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol b a d) /\ ((euclidean__axioms.nCol b d a) /\ ((euclidean__axioms.nCol d a b) /\ ((euclidean__axioms.nCol a d b) /\ (euclidean__axioms.nCol d b a))))) as H49.
----------------------------------------- apply (@lemma__NCorder.lemma__NCorder a b d H23).
----------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H54.
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA d a b d a b) as H50.
----------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive d a b H49).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA d a b f a e) as H51.
------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper d a b d a b f e H50 H47 H48).
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA f a e d a b) as H52.
------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric d a b f a e H51).
------------------------------------------- assert (* Cut *) (euclidean__defs.Per f a e) as H53.
-------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright d a b f a e H43 H52).
-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA f a e D A B) as H54.
--------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 f a e D A B H53 H44).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong f e D B) as H55.
---------------------------------------------- assert (* Cut *) (forall A0 B0 C0 a0 b0 c0, (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H55.
----------------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
------------------------------------------------ apply (@proposition__04.proposition__04 A0 B0 C0 a0 b0 c0 __ __0 __1).
------------------------------------------------ destruct __2 as [__2 __3].
exact __2.
----------------------------------------------- apply (@H55 a f e A D B H42 H36 H54).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong f a D A) as H56.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong f a D A) /\ ((euclidean__axioms.Cong f a A D) /\ (euclidean__axioms.Cong a f D A))) as H56.
------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip a f A D H42).
------------------------------------------------ destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H57.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 f a e D A B) as H57.
------------------------------------------------ split.
------------------------------------------------- exact H56.
------------------------------------------------- split.
-------------------------------------------------- exact H36.
-------------------------------------------------- exact H55.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET f a e D A B) as H58.
------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal f a e D A B H57).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e A B D) as H59.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET f a e A B D) /\ ((euclidean__axioms.ET f a e D B A) /\ ((euclidean__axioms.ET f a e A D B) /\ ((euclidean__axioms.ET f a e B A D) /\ (euclidean__axioms.ET f a e B D A))))) as H59.
--------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation f a e D A B H58).
--------------------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D f a e) as H60.
--------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric f a e A B D H59).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e a b d) as H61.
---------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive f a e a b d A B D H59 H26).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET f a e d a b) as H62.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET f a e b d a) /\ ((euclidean__axioms.ET f a e a d b) /\ ((euclidean__axioms.ET f a e b a d) /\ ((euclidean__axioms.ET f a e d b a) /\ (euclidean__axioms.ET f a e d a b))))) as H62.
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation f a e a b d H61).
------------------------------------------------------ destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H70.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET d a b f a e) as H63.
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric f a e d a b H62).
------------------------------------------------------ assert (euclidean__axioms.Triangle d a b) as H64 by exact H49.
assert (* Cut *) (~(euclidean__axioms.ET d a b f a e)) as H65.
------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt2 d a b f e H64 H41 H35).
------------------------------------------------------- apply (@H65 H63).
------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H33.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H33.
--------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B D H21).
--------------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H34.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq a b) as H34.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b d) /\ ((euclidean__axioms.neq a d) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq d b) /\ (euclidean__axioms.neq d a)))))) as H34.
---------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct a b d H23).
---------------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H35.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B a b) as H35.
---------------------------------- apply (@lemma__trichotomy1.lemma__trichotomy1 A B a b H32 H31 H33 H34).
---------------------------------- exact H35.
Qed.
