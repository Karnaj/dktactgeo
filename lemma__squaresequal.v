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
Definition lemma__squaresequal : forall A B C D a b c d, (euclidean__axioms.Cong A B a b) -> ((euclidean__defs.SQ A B C D) -> ((euclidean__defs.SQ a b c d) -> (euclidean__axioms.EF A B C D a b c d))).
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
- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H0 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H20.
- assert (* Cut *) (euclidean__defs.Per d a b) as H3.
-- destruct H1 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H0 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H9.
-- assert (* Cut *) (euclidean__defs.CongA D A B d a b) as H4.
--- apply (@lemma__Euclid4.lemma__Euclid4 D A B d a b H2 H3).
--- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H5.
---- destruct H1 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H0 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
---- assert (* Cut *) (euclidean__axioms.Cong a b d a) as H6.
----- destruct H1 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H0 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H10.
----- assert (* Cut *) (euclidean__axioms.Cong D A A B) as H7.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D A B A H5).
------ assert (* Cut *) (euclidean__axioms.Cong D A a b) as H8.
------- apply (@lemma__congruencetransitive.lemma__congruencetransitive D A A B a b H7 H).
------- assert (* Cut *) (euclidean__axioms.Cong D A d a) as H9.
-------- apply (@lemma__congruencetransitive.lemma__congruencetransitive D A a b d a H8 H6).
-------- assert (* Cut *) (euclidean__defs.PG A B C D) as H10.
--------- apply (@lemma__squareparallelogram.lemma__squareparallelogram A B C D H0).
--------- assert (* Cut *) (euclidean__defs.PG a b c d) as H11.
---------- apply (@lemma__squareparallelogram.lemma__squareparallelogram a b c d H1).
---------- assert (* Cut *) (euclidean__defs.Par A B C D) as H12.
----------- destruct H11 as [H12 H13].
destruct H10 as [H14 H15].
exact H14.
----------- assert (* Cut *) (euclidean__defs.Par a b c d) as H13.
------------ destruct H11 as [H13 H14].
destruct H10 as [H15 H16].
exact H13.
------------ assert (* Cut *) (euclidean__axioms.nCol A B D) as H14.
------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H14.
-------------- apply (@lemma__parallelNC.lemma__parallelNC A B C D H12).
-------------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
------------- assert (* Cut *) (euclidean__axioms.nCol a b d) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.nCol a b c) /\ ((euclidean__axioms.nCol a c d) /\ ((euclidean__axioms.nCol b c d) /\ (euclidean__axioms.nCol a b d)))) as H15.
--------------- apply (@lemma__parallelNC.lemma__parallelNC a b c d H13).
--------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H21.
-------------- assert (* Cut *) (euclidean__axioms.Cong A D a d) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.Cong A D a d) /\ ((euclidean__axioms.Cong A D d a) /\ (euclidean__axioms.Cong D A a d))) as H16.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip D A d a H9).
---------------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H17.
--------------- assert (* Cut *) (euclidean__axioms.Cong D B d b) as H17.
---------------- assert (* Cut *) (forall A0 B0 C0 a0 b0 c0, (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H17.
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
------------------ apply (@proposition__04.proposition__04 A0 B0 C0 a0 b0 c0 __ __0 __1).
------------------ destruct __2 as [__2 __3].
exact __2.
----------------- apply (@H17 A D B a d b H16 H H4).
---------------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H18.
----------------- assert (* Cut *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H18.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip D B d b H17).
------------------ destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H19.
----------------- assert (euclidean__axioms.Triangle A B D) as H19 by exact H14.
assert (* Cut *) (euclidean__axioms.Cong__3 A B D a b d) as H20.
------------------ split.
------------------- exact H.
------------------- split.
-------------------- exact H18.
-------------------- exact H16.
------------------ assert (* Cut *) (euclidean__axioms.ET A B D a b d) as H21.
------------------- apply (@euclidean__axioms.axiom__congruentequal A B D a b d H20).
------------------- assert (* Cut *) (euclidean__axioms.ET A B D b d a) as H22.
-------------------- assert (* Cut *) ((euclidean__axioms.ET A B D b d a) /\ ((euclidean__axioms.ET A B D a d b) /\ ((euclidean__axioms.ET A B D b a d) /\ ((euclidean__axioms.ET A B D d b a) /\ (euclidean__axioms.ET A B D d a b))))) as H22.
--------------------- apply (@euclidean__axioms.axiom__ETpermutation A B D a b d H21).
--------------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
-------------------- assert (* Cut *) (euclidean__axioms.ET b d a A B D) as H23.
--------------------- apply (@euclidean__axioms.axiom__ETsymmetric A B D b d a H22).
--------------------- assert (* Cut *) (euclidean__axioms.ET b d a B D A) as H24.
---------------------- assert (* Cut *) ((euclidean__axioms.ET b d a B D A) /\ ((euclidean__axioms.ET b d a A D B) /\ ((euclidean__axioms.ET b d a B A D) /\ ((euclidean__axioms.ET b d a D B A) /\ (euclidean__axioms.ET b d a D A B))))) as H24.
----------------------- apply (@euclidean__axioms.axiom__ETpermutation b d a A B D H23).
----------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
---------------------- assert (* Cut *) (euclidean__axioms.ET B D A b d a) as H25.
----------------------- apply (@euclidean__axioms.axiom__ETsymmetric b d a B D A H24).
----------------------- assert (* Cut *) (euclidean__axioms.Cong A B B C) as H26.
------------------------ destruct H1 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H0 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H40.
------------------------ assert (* Cut *) (euclidean__axioms.Cong a b b c) as H27.
------------------------- destruct H1 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H0 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H29.
------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H28.
-------------------------- destruct H1 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H0 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H40.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong a b c d) as H29.
--------------------------- destruct H1 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H0 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H29.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B C A B) as H30.
---------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B A B C H26).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong B C a b) as H31.
----------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B C A B a b H30 H).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H32.
------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive B C a b b c H31 H27).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong C D A B) as H33.
------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C A B D H28).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D a b) as H34.
-------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C D A B a b H33 H).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D c d) as H35.
--------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C D a b c d H34 H29).
--------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H36.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H36.
----------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B C D H12).
----------------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
---------------------------------- assert (euclidean__axioms.Triangle B C D) as H37 by exact H36.
assert (* Cut *) (euclidean__axioms.Cong__3 B C D b c d) as H38.
----------------------------------- split.
------------------------------------ exact H32.
------------------------------------ split.
------------------------------------- exact H35.
------------------------------------- exact H18.
----------------------------------- assert (* Cut *) (euclidean__axioms.ET B C D b c d) as H39.
------------------------------------ apply (@euclidean__axioms.axiom__congruentequal B C D b c d H38).
------------------------------------ assert (* Cut *) (euclidean__axioms.ET B C D b d c) as H40.
------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B C D c d b) /\ ((euclidean__axioms.ET B C D b d c) /\ ((euclidean__axioms.ET B C D c b d) /\ ((euclidean__axioms.ET B C D d c b) /\ (euclidean__axioms.ET B C D d b c))))) as H40.
-------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation B C D b c d H39).
-------------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H43.
------------------------------------- assert (* Cut *) (euclidean__axioms.ET b d c B C D) as H41.
-------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric B C D b d c H40).
-------------------------------------- assert (* Cut *) (euclidean__axioms.ET b d c B D C) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.ET b d c C D B) /\ ((euclidean__axioms.ET b d c B D C) /\ ((euclidean__axioms.ET b d c C B D) /\ ((euclidean__axioms.ET b d c D C B) /\ (euclidean__axioms.ET b d c D B C))))) as H42.
---------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation b d c B C D H41).
---------------------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H45.
--------------------------------------- assert (* Cut *) (euclidean__axioms.ET B D C b d c) as H43.
---------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric b d c B D C H42).
---------------------------------------- assert (* Cut *) (euclidean__defs.RE A B C D) as H44.
----------------------------------------- apply (@lemma__squarerectangle.lemma__squarerectangle A B C D H0).
----------------------------------------- assert (* Cut *) (euclidean__defs.CR A C B D) as H45.
------------------------------------------ destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
------------------------------------------ assert (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H46 by exact H45.
destruct H46 as [M H47].
destruct H47 as [H48 H49].
assert (* Cut *) (euclidean__defs.RE a b c d) as H50.
------------------------------------------- apply (@lemma__squarerectangle.lemma__squarerectangle a b c d H1).
------------------------------------------- assert (* Cut *) (euclidean__defs.CR a c b d) as H51.
-------------------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H44 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H58.
-------------------------------------------- assert (exists m, (euclidean__axioms.BetS a m c) /\ (euclidean__axioms.BetS b m d)) as H52 by exact H51.
destruct H52 as [m H53].
destruct H53 as [H54 H55].
assert (* Cut *) (euclidean__axioms.EF B A D C b a d c) as H56.
--------------------------------------------- apply (@euclidean__axioms.axiom__paste3 B D A C M b d a c m H25 H43 H48).
----------------------------------------------left.
exact H49.

---------------------------------------------- exact H54.
----------------------------------------------left.
exact H55.

--------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B A D C a b c d) as H57.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B A D C a d c b) /\ ((euclidean__axioms.EF B A D C c d a b) /\ ((euclidean__axioms.EF B A D C d c b a) /\ ((euclidean__axioms.EF B A D C a b c d) /\ ((euclidean__axioms.EF B A D C c b a d) /\ ((euclidean__axioms.EF B A D C d a b c) /\ (euclidean__axioms.EF B A D C b c d a))))))) as H57.
----------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation B A D C b a d c H56).
----------------------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H64.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b c d B A D C) as H58.
----------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric B A D C a b c d H57).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b c d A B C D) as H59.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.EF a b c d A D C B) /\ ((euclidean__axioms.EF a b c d C D A B) /\ ((euclidean__axioms.EF a b c d D C B A) /\ ((euclidean__axioms.EF a b c d A B C D) /\ ((euclidean__axioms.EF a b c d C B A D) /\ ((euclidean__axioms.EF a b c d D A B C) /\ (euclidean__axioms.EF a b c d B C D A))))))) as H59.
------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation a b c d B A D C H58).
------------------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H66.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A B C D a b c d) as H60.
------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric a b c d A B C D H59).
------------------------------------------------- exact H60.
Qed.
