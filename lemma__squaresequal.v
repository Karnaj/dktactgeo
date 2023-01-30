Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__Euclid4.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__parallelNC.
Require Export lemma__squareparallelogram.
Require Export lemma__squarerectangle.
Require Export logic.
Require Export proposition__04.
Definition lemma__squaresequal : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.Cong A B a b) -> ((euclidean__defs.SQ A B C D) -> ((euclidean__defs.SQ a b c d) -> (euclidean__axioms.EF A B C D a b c d))).
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
assert (* Cut *) (euclidean__defs.Per D A B) as H2.
- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H2.
-- exact H1.
-- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H4.
--- exact H3.
--- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H6.
---- exact H5.
---- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H8.
----- exact H7.
----- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H10.
------ exact H9.
------ destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H12.
------- exact H11.
------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H14.
-------- exact H0.
-------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H16.
--------- exact H15.
--------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H18.
---------- exact H17.
---------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H20.
----------- exact H19.
----------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H22.
------------ exact H21.
------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H24.
------------- exact H23.
------------- destruct H24 as [H24 H25].
exact H20.
- assert (* Cut *) (euclidean__defs.Per d a b) as H3.
-- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H3.
--- exact H1.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H15.
--------- exact H0.
--------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H17.
---------- exact H16.
---------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H19.
----------- exact H18.
----------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H21.
------------ exact H20.
------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H23.
------------- exact H22.
------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H25.
-------------- exact H24.
-------------- destruct H25 as [H25 H26].
exact H9.
-- assert (* Cut *) (euclidean__defs.CongA D A B d a b) as H4.
--- apply (@lemma__Euclid4.lemma__Euclid4 (D) (A) (B) (d) (a) (b) (H2) H3).
--- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H5.
---- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H5.
----- exact H1.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H17.
----------- exact H0.
----------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H21.
------------- exact H20.
------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H23.
-------------- exact H22.
-------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H27.
---------------- exact H26.
---------------- destruct H27 as [H27 H28].
exact H21.
---- assert (* Cut *) (euclidean__axioms.Cong a b d a) as H6.
----- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H6.
------ exact H1.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H18.
------------ exact H0.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H26.
---------------- exact H25.
---------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H28.
----------------- exact H27.
----------------- destruct H28 as [H28 H29].
exact H10.
----- assert (* Cut *) (euclidean__axioms.Cong D A A B) as H7.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (B) (A) H5).
------ assert (* Cut *) (euclidean__axioms.Cong D A a b) as H8.
------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (D) (A) (A) (B) (a) (b) (H7) H).
------- assert (* Cut *) (euclidean__axioms.Cong D A d a) as H9.
-------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (D) (A) (a) (b) (d) (a) (H8) H6).
-------- assert (* Cut *) (euclidean__defs.PG A B C D) as H10.
--------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (A) (B) (C) (D) H0).
--------- assert (* Cut *) (euclidean__defs.PG a b c d) as H11.
---------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (a) (b) (c) (d) H1).
---------- assert (* Cut *) (euclidean__defs.Par A B C D) as H12.
----------- assert (* AndElim *) ((euclidean__defs.Par a b c d) /\ (euclidean__defs.Par a d b c)) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
------------- exact H10.
------------- destruct H14 as [H14 H15].
exact H14.
----------- assert (* Cut *) (euclidean__defs.Par a b c d) as H13.
------------ assert (* AndElim *) ((euclidean__defs.Par a b c d) /\ (euclidean__defs.Par a d b c)) as H13.
------------- exact H11.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
-------------- exact H10.
-------------- destruct H15 as [H15 H16].
exact H13.
------------ assert (* Cut *) (euclidean__axioms.nCol A B D) as H14.
------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H14.
-------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H12).
-------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
exact H20.
------------- assert (* Cut *) (euclidean__axioms.nCol a b d) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H15.
--------------- apply (@lemma__parallelNC.lemma__parallelNC (a) (b) (c) (d) H13).
--------------- assert (* AndElim *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
exact H21.
-------------- assert (* Cut *) (euclidean__axioms.Cong A D a d) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.Cong A D a d) /\ ((euclidean__axioms.Cong A D d a) /\ (euclidean__axioms.Cong D A a d))) as H16.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (A) (d) (a) H9).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong A D a d) /\ ((euclidean__axioms.Cong A D d a) /\ (euclidean__axioms.Cong D A a d))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong A D d a) /\ (euclidean__axioms.Cong D A a d)) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
exact H17.
--------------- assert (* Cut *) (euclidean__axioms.Cong D B d b) as H17.
---------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H17.
----------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
------------------ apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a0) (b0) (c0) (__) (__0) __1).
------------------ destruct __2 as [__2 __3].
exact __2.
----------------- apply (@H17 (A) (D) (B) (a) (d) (b) (H16) (H) H4).
---------------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H18.
----------------- assert (* Cut *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H18.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (d) (b) H17).
------------------ assert (* AndElim *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d)) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
exact H19.
----------------- assert (* Cut *) (euclidean__axioms.Triangle A B D) as H19.
------------------ exact H14.
------------------ assert (* Cut *) (euclidean__axioms.Cong__3 A B D a b d) as H20.
------------------- split.
-------------------- exact H.
-------------------- split.
--------------------- exact H18.
--------------------- exact H16.
------------------- assert (* Cut *) (euclidean__axioms.ET A B D a b d) as H21.
-------------------- apply (@euclidean__axioms.axiom__congruentequal (A) (B) (D) (a) (b) (d) H20).
-------------------- assert (* Cut *) (euclidean__axioms.ET A B D b d a) as H22.
--------------------- assert (* Cut *) ((euclidean__axioms.ET A B D b d a) /\ ((euclidean__axioms.ET A B D a d b) /\ ((euclidean__axioms.ET A B D b a d) /\ ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b))))) as H22.
---------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (D) (a) (b) (d) H21).
---------------------- assert (* AndElim *) ((euclidean__axioms.ET A B D b d a) /\ ((euclidean__axioms.ET A B D a d b) /\ ((euclidean__axioms.ET A B D b a d) /\ ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b))))) as H23.
----------------------- exact H22.
----------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.ET A B D a d b) /\ ((euclidean__axioms.ET A B D b a d) /\ ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b)))) as H25.
------------------------ exact H24.
------------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.ET A B D b a d) /\ ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b)) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
exact H23.
--------------------- assert (* Cut *) (euclidean__axioms.ET b d a A B D) as H23.
---------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (D) (b) (d) (a) H22).
---------------------- assert (* Cut *) (euclidean__axioms.ET b d a B D A) as H24.
----------------------- assert (* Cut *) ((euclidean__axioms.ET b d a B D A) /\ ((euclidean__axioms.ET b d a A D B) /\ ((euclidean__axioms.ET b d a B A D) /\ ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B))))) as H24.
------------------------ apply (@euclidean__axioms.axiom__ETpermutation (b) (d) (a) (A) (B) (D) H23).
------------------------ assert (* AndElim *) ((euclidean__axioms.ET b d a B D A) /\ ((euclidean__axioms.ET b d a A D B) /\ ((euclidean__axioms.ET b d a B A D) /\ ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B))))) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.ET b d a A D B) /\ ((euclidean__axioms.ET b d a B A D) /\ ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B)))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.ET b d a B A D) /\ ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B))) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B)) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
exact H25.
----------------------- assert (* Cut *) (euclidean__axioms.ET B D A b d a) as H25.
------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (b) (d) (a) (B) (D) (A) H24).
------------------------ assert (* Cut *) (euclidean__axioms.Cong A B B C) as H26.
------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H26.
-------------------------- exact H1.
-------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H28.
--------------------------- exact H27.
--------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H38.
-------------------------------- exact H0.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
exact H40.
------------------------- assert (* Cut *) (euclidean__axioms.Cong a b b c) as H27.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H27.
--------------------------- exact H1.
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
--------------------------------- exact H0.
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
exact H29.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H28.
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H28.
---------------------------- exact H1.
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
---------------------------------- exact H0.
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
exact H40.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong a b c d) as H29.
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong a b c d) /\ ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))))) as H29.
----------------------------- exact H1.
----------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Cong a b b c) /\ ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))))) as H31.
------------------------------ exact H30.
------------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Cong a b d a) /\ ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))))) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)))) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ (euclidean__defs.Per c d a)) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H41.
----------------------------------- exact H0.
----------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H45.
------------------------------------- exact H44.
------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H47.
-------------------------------------- exact H46.
-------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H49.
--------------------------------------- exact H48.
--------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H51.
---------------------------------------- exact H50.
---------------------------------------- destruct H51 as [H51 H52].
exact H29.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong B C A B) as H30.
----------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (B) (C) H26).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B C a b) as H31.
------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (A) (B) (a) (b) (H30) H).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong B C b c) as H32.
------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (a) (b) (b) (c) (H31) H27).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D A B) as H33.
-------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (A) (B) (D) H28).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D a b) as H34.
--------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (D) (A) (B) (a) (b) (H33) H).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D c d) as H35.
---------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (D) (a) (b) (c) (d) (H34) H29).
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H36.
----------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H36.
------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H12).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H37.
------------------------------------- exact H36.
------------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H39.
-------------------------------------- exact H38.
-------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
exact H41.
----------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B C D) as H37.
------------------------------------ exact H36.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 B C D b c d) as H38.
------------------------------------- split.
-------------------------------------- exact H32.
-------------------------------------- split.
--------------------------------------- exact H35.
--------------------------------------- exact H18.
------------------------------------- assert (* Cut *) (euclidean__axioms.ET B C D b c d) as H39.
-------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (B) (C) (D) (b) (c) (d) H38).
-------------------------------------- assert (* Cut *) (euclidean__axioms.ET B C D b d c) as H40.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B C D c d b) /\ ((euclidean__axioms.ET B C D b d c) /\ ((euclidean__axioms.ET B C D c b d) /\ ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c))))) as H40.
---------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (B) (C) (D) (b) (c) (d) H39).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET B C D c d b) /\ ((euclidean__axioms.ET B C D b d c) /\ ((euclidean__axioms.ET B C D c b d) /\ ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c))))) as H41.
----------------------------------------- exact H40.
----------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.ET B C D b d c) /\ ((euclidean__axioms.ET B C D c b d) /\ ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c)))) as H43.
------------------------------------------ exact H42.
------------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.ET B C D c b d) /\ ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c))) as H45.
------------------------------------------- exact H44.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c)) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
exact H43.
--------------------------------------- assert (* Cut *) (euclidean__axioms.ET b d c B C D) as H41.
---------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (B) (C) (D) (b) (d) (c) H40).
---------------------------------------- assert (* Cut *) (euclidean__axioms.ET b d c B D C) as H42.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.ET b d c C D B) /\ ((euclidean__axioms.ET b d c B D C) /\ ((euclidean__axioms.ET b d c C B D) /\ ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C))))) as H42.
------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (b) (d) (c) (B) (C) (D) H41).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET b d c C D B) /\ ((euclidean__axioms.ET b d c B D C) /\ ((euclidean__axioms.ET b d c C B D) /\ ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C))))) as H43.
------------------------------------------- exact H42.
------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.ET b d c B D C) /\ ((euclidean__axioms.ET b d c C B D) /\ ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C)))) as H45.
-------------------------------------------- exact H44.
-------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.ET b d c C B D) /\ ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C)) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
exact H45.
----------------------------------------- assert (* Cut *) (euclidean__axioms.ET B D C b d c) as H43.
------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (b) (d) (c) (B) (D) (C) H42).
------------------------------------------ assert (* Cut *) (euclidean__defs.RE A B C D) as H44.
------------------------------------------- apply (@lemma__squarerectangle.lemma__squarerectangle (A) (B) (C) (D) H0).
------------------------------------------- assert (* Cut *) (euclidean__defs.CR A C B D) as H45.
-------------------------------------------- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H45.
--------------------------------------------- exact H44.
--------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H47.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H49.
----------------------------------------------- exact H48.
----------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H51.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H51 as [H51 H52].
exact H52.
-------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H46.
--------------------------------------------- exact H45.
--------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H47.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H47 as [M H47].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H48.
----------------------------------------------- exact H47.
----------------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) (euclidean__defs.RE a b c d) as H50.
------------------------------------------------ apply (@lemma__squarerectangle.lemma__squarerectangle (a) (b) (c) (d) H1).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CR a c b d) as H51.
------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Per d a b) /\ ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))))) as H51.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.Per a b c) /\ ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)))) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__defs.Per b c d) /\ ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d))) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__defs.Per c d a) /\ (euclidean__defs.CR a c b d)) as H57.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H59.
------------------------------------------------------ exact H44.
------------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H61.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H63.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
exact H58.
------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS a m c) /\ (euclidean__axioms.BetS b m d)) as H52.
-------------------------------------------------- exact H51.
-------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS a m c) /\ (euclidean__axioms.BetS b m d))) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [m H53].
assert (* AndElim *) ((euclidean__axioms.BetS a m c) /\ (euclidean__axioms.BetS b m d)) as H54.
---------------------------------------------------- exact H53.
---------------------------------------------------- destruct H54 as [H54 H55].
assert (* Cut *) (euclidean__axioms.EF B A D C b a d c) as H56.
----------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 (B) (D) (A) (C) (M) (b) (d) (a) (c) (m) (H25) (H43) (H48)).
------------------------------------------------------left.
exact H49.

------------------------------------------------------ exact H54.
------------------------------------------------------left.
exact H55.

----------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B A D C a b c d) as H57.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.EF B A D C a d c b) /\ ((euclidean__axioms.EF B A D C c d a b) /\ ((euclidean__axioms.EF B A D C d c b a) /\ ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a))))))) as H57.
------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (B) (A) (D) (C) (b) (a) (d) (c) H56).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF B A D C a d c b) /\ ((euclidean__axioms.EF B A D C c d a b) /\ ((euclidean__axioms.EF B A D C d c b a) /\ ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a))))))) as H58.
-------------------------------------------------------- exact H57.
-------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.EF B A D C c d a b) /\ ((euclidean__axioms.EF B A D C d c b a) /\ ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a)))))) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF B A D C d c b a) /\ ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a))))) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a)))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a))) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a)) as H68.
------------------------------------------------------------- exact H67.
------------------------------------------------------------- destruct H68 as [H68 H69].
exact H64.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF a b c d B A D C) as H58.
------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (B) (A) (D) (C) (a) (b) (c) (d) H57).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b c d A B C D) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF a b c d A D C B) /\ ((euclidean__axioms.EF a b c d C D A B) /\ ((euclidean__axioms.EF a b c d D C B A) /\ ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A))))))) as H59.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (a) (b) (c) (d) (B) (A) (D) (C) H58).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF a b c d A D C B) /\ ((euclidean__axioms.EF a b c d C D A B) /\ ((euclidean__axioms.EF a b c d D C B A) /\ ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A))))))) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF a b c d C D A B) /\ ((euclidean__axioms.EF a b c d D C B A) /\ ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A)))))) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF a b c d D C B A) /\ ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A))))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A)))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A)) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
exact H66.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D a b c d) as H60.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (a) (b) (c) (d) (A) (B) (C) (D) H59).
--------------------------------------------------------- exact H60.
Qed.
