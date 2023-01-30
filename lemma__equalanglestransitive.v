Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__angledistinct.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray4.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Definition lemma__equalanglestransitive : forall A B C D E F P Q R, (euclidean__defs.CongA A B C D E F) -> ((euclidean__defs.CongA D E F P Q R) -> (euclidean__defs.CongA A B C P Q R)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro R.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A B) as H1.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H1.
-- apply (@lemma__angledistinct.lemma__angledistinct A B C D E F H).
-- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H2.
- assert (* Cut *) (euclidean__axioms.neq D E) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H2.
--- apply (@lemma__angledistinct.lemma__angledistinct D E F P Q R H0).
--- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H3.
-- assert (* Cut *) (euclidean__axioms.neq B A) as H3.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H1).
--- assert (* Cut *) (euclidean__axioms.neq E D) as H4.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D E H2).
---- assert (* Cut *) (euclidean__axioms.neq E F) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H5.
------ apply (@lemma__angledistinct.lemma__angledistinct D E F P Q R H0).
------ destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.neq B C) as H6.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H6.
------- apply (@lemma__angledistinct.lemma__angledistinct A B C D E F H).
------- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H9.
------ assert (* Cut *) (euclidean__axioms.neq P Q) as H7.
------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq P R)))))) as H7.
-------- apply (@lemma__angledistinct.lemma__angledistinct D E F P Q R H0).
-------- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.neq Q P) as H8.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P Q H7).
-------- assert (* Cut *) (exists U, (euclidean__defs.Out E D U) /\ (euclidean__axioms.Cong E U B A)) as H9.
--------- apply (@lemma__layoff.lemma__layoff E D B A H4 H3).
--------- destruct H9 as [U H10].
destruct H10 as [H11 H12].
assert (* Cut *) (exists V, (euclidean__defs.Out E F V) /\ (euclidean__axioms.Cong E V B C)) as H13.
---------- apply (@lemma__layoff.lemma__layoff E F B C H5 H6).
---------- destruct H13 as [V H14].
destruct H14 as [H15 H16].
assert (* Cut *) (euclidean__axioms.neq E U) as H17.
----------- apply (@lemma__raystrict.lemma__raystrict E D U H11).
----------- assert (* Cut *) (euclidean__axioms.neq E V) as H18.
------------ apply (@lemma__raystrict.lemma__raystrict E F V H15).
------------ assert (* Cut *) (euclidean__defs.CongA P Q R D E F) as H19.
------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D E F P Q R H0).
------------- assert (* Cut *) (euclidean__axioms.neq Q R) as H20.
-------------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H20.
--------------- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H19).
--------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
-------------- assert (* Cut *) (exists u, (euclidean__defs.Out Q P u) /\ (euclidean__axioms.Cong Q u E U)) as H21.
--------------- apply (@lemma__layoff.lemma__layoff Q P E U H8 H17).
--------------- destruct H21 as [u H22].
destruct H22 as [H23 H24].
assert (* Cut *) (exists v, (euclidean__defs.Out Q R v) /\ (euclidean__axioms.Cong Q v E V)) as H25.
---------------- apply (@lemma__layoff.lemma__layoff Q R E V H20 H18).
---------------- destruct H25 as [v H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__axioms.nCol A B C) as H29.
----------------- assert (exists U0 V0 u0 v0, (euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q U0 E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol P Q R)))))))) as H29 by exact H19.
assert (exists U0 V0 u0 v0, (euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong Q U0 E u0) /\ ((euclidean__axioms.Cong Q V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol P Q R)))))))) as __TmpHyp by exact H29.
destruct __TmpHyp as [x H30].
destruct H30 as [x0 H31].
destruct H31 as [x1 H32].
destruct H32 as [x2 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
assert (exists U0 V0 u0 v0, (euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E U0 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol D E F)))))))) as H48 by exact H0.
assert (exists U0 V0 u0 v0, (euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ ((euclidean__defs.Out Q P u0) /\ ((euclidean__defs.Out Q R v0) /\ ((euclidean__axioms.Cong E U0 Q u0) /\ ((euclidean__axioms.Cong E V0 Q v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol D E F)))))))) as __TmpHyp0 by exact H48.
destruct __TmpHyp0 as [x3 H49].
destruct H49 as [x4 H50].
destruct H50 as [x5 H51].
destruct H51 as [x6 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
assert (exists U0 V0 u0 v0, (euclidean__defs.Out B A U0) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B U0 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol A B C)))))))) as H67 by exact H.
assert (exists U0 V0 u0 v0, (euclidean__defs.Out B A U0) /\ ((euclidean__defs.Out B C V0) /\ ((euclidean__defs.Out E D u0) /\ ((euclidean__defs.Out E F v0) /\ ((euclidean__axioms.Cong B U0 E u0) /\ ((euclidean__axioms.Cong B V0 E v0) /\ ((euclidean__axioms.Cong U0 V0 u0 v0) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp1 by exact H67.
destruct __TmpHyp1 as [x7 H68].
destruct H68 as [x8 H69].
destruct H69 as [x9 H70].
destruct H70 as [x10 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H85.
----------------- assert (* Cut *) (euclidean__defs.CongA A B C U E V) as H30.
------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper A B C D E F U V H H11 H15).
------------------ assert (* Cut *) (euclidean__axioms.Cong B A E U) as H31.
------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B E U A H12).
------------------- assert (* Cut *) (euclidean__axioms.Cong B C E V) as H32.
-------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B E V C H16).
-------------------- assert (* Cut *) ((euclidean__axioms.Cong A C U V) /\ ((euclidean__defs.CongA B A C E U V) /\ (euclidean__defs.CongA B C A E V U))) as H33.
--------------------- apply (@proposition__04.proposition__04 B A C E U V H31 H32 H30).
--------------------- assert (* Cut *) (euclidean__axioms.Cong E U Q u) as H34.
---------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E Q u U H24).
---------------------- assert (* Cut *) (euclidean__axioms.Cong E V Q v) as H35.
----------------------- destruct H33 as [H35 H36].
destruct H36 as [H37 H38].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E Q v V H28).
----------------------- assert (* Cut *) (euclidean__defs.CongA D E F u Q v) as H36.
------------------------ destruct H33 as [H36 H37].
destruct H37 as [H38 H39].
apply (@lemma__equalangleshelper.lemma__equalangleshelper D E F P Q R u v H0 H23 H27).
------------------------ assert (* Cut *) (euclidean__defs.CongA u Q v D E F) as H37.
------------------------- destruct H33 as [H37 H38].
destruct H38 as [H39 H40].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D E F u Q v H36).
------------------------- assert (* Cut *) (euclidean__defs.CongA u Q v U E V) as H38.
-------------------------- destruct H33 as [H38 H39].
destruct H39 as [H40 H41].
apply (@lemma__equalangleshelper.lemma__equalangleshelper u Q v D E F U V H37 H11 H15).
-------------------------- assert (* Cut *) (euclidean__defs.CongA U E V u Q v) as H39.
--------------------------- destruct H33 as [H39 H40].
destruct H40 as [H41 H42].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric u Q v U E V H38).
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong U V u v) /\ ((euclidean__defs.CongA E U V Q u v) /\ (euclidean__defs.CongA E V U Q v u))) as H40.
---------------------------- destruct H33 as [H40 H41].
destruct H41 as [H42 H43].
apply (@proposition__04.proposition__04 E U V Q u v H34 H35 H39).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A C u v) as H41.
----------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H33 as [H45 H46].
destruct H46 as [H47 H48].
apply (@lemma__congruencetransitive.lemma__congruencetransitive A C U V u v H45 H41).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B A Q u) as H42.
------------------------------ destruct H40 as [H42 H43].
destruct H43 as [H44 H45].
destruct H33 as [H46 H47].
destruct H47 as [H48 H49].
apply (@lemma__congruencetransitive.lemma__congruencetransitive B A E U Q u H31 H34).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong B C Q v) as H43.
------------------------------- destruct H40 as [H43 H44].
destruct H44 as [H45 H46].
destruct H33 as [H47 H48].
destruct H48 as [H49 H50].
apply (@lemma__congruencetransitive.lemma__congruencetransitive B C E V Q v H32 H35).
------------------------------- assert (* Cut *) (A = A) as H44.
-------------------------------- destruct H40 as [H44 H45].
destruct H45 as [H46 H47].
destruct H33 as [H48 H49].
destruct H49 as [H50 H51].
apply (@logic.eq__refl Point A).
-------------------------------- assert (* Cut *) (C = C) as H45.
--------------------------------- destruct H40 as [H45 H46].
destruct H46 as [H47 H48].
destruct H33 as [H49 H50].
destruct H50 as [H51 H52].
apply (@logic.eq__refl Point C).
--------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H46.
---------------------------------- destruct H40 as [H46 H47].
destruct H47 as [H48 H49].
destruct H33 as [H50 H51].
destruct H51 as [H52 H53].
apply (@lemma__ray4.lemma__ray4 B A A).
-----------------------------------right.
left.
exact H44.

----------------------------------- exact H3.
---------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H47.
----------------------------------- destruct H40 as [H47 H48].
destruct H48 as [H49 H50].
destruct H33 as [H51 H52].
destruct H52 as [H53 H54].
apply (@lemma__ray4.lemma__ray4 B C C).
------------------------------------right.
left.
exact H45.

------------------------------------ exact H6.
----------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C P Q R) as H48.
------------------------------------ exists A.
exists C.
exists u.
exists v.
split.
------------------------------------- exact H46.
------------------------------------- split.
-------------------------------------- exact H47.
-------------------------------------- split.
--------------------------------------- exact H23.
--------------------------------------- split.
---------------------------------------- exact H27.
---------------------------------------- split.
----------------------------------------- exact H42.
----------------------------------------- split.
------------------------------------------ exact H43.
------------------------------------------ split.
------------------------------------------- exact H41.
------------------------------------------- exact H29.
------------------------------------ exact H48.
Qed.
