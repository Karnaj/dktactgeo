Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__angledistinct.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__03.
Require Export proposition__04.
Definition lemma__angleorderrespectscongruence : forall A B C D E F P Q R, (euclidean__defs.LtA A B C D E F) -> ((euclidean__defs.CongA P Q R D E F) -> (euclidean__defs.LtA A B C P Q R)).
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
assert (exists G H1 J, (euclidean__axioms.BetS G H1 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H1)))) as H1 by exact H.
destruct H1 as [G H2].
destruct H2 as [H3 H4].
destruct H4 as [J H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
- split.
-- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
--- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H0).
--- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H13.
-- split.
--- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
---- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H0).
---- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H15.
--- split.
---- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
----- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H0).
----- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H17.
---- split.
----- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H12.
------ apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
------ destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H19.
----- split.
------ assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
------- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H0).
------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H21.
------ assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
------- apply (@lemma__angledistinct.lemma__angledistinct P Q R D E F H0).
------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H22.
- assert (* Cut *) (euclidean__axioms.neq Q P) as H13.
-- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P Q H13).
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H14.
--- destruct H12 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
split.
---- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
----- apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
----- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H25.
---- split.
----- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
------ apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
------ destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H27.
----- split.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
------- apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H29.
------ split.
------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
-------- apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
-------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H20.
------- split.
-------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
--------- apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
--------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H33.
-------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
--------- apply (@lemma__angledistinct.lemma__angledistinct A B C D E H3 H11).
--------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H34.
--- assert (* Cut *) (euclidean__axioms.neq E G) as H15.
---- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H12 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
apply (@lemma__raystrict.lemma__raystrict E D G H8).
---- assert (* Cut *) (exists U, (euclidean__defs.Out Q P U) /\ (euclidean__axioms.Cong Q U E G)) as H16.
----- destruct H14 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H12 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
apply (@lemma__layoff.lemma__layoff Q P E G H13 H15).
----- destruct H16 as [U H17].
destruct H17 as [H18 H19].
destruct H14 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H12 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
assert (* Cut *) (euclidean__axioms.neq E J) as H40.
------ apply (@lemma__raystrict.lemma__raystrict E F J H10).
------ assert (* Cut *) (exists V, (euclidean__defs.Out Q R V) /\ (euclidean__axioms.Cong Q V E J)) as H41.
------- apply (@lemma__layoff.lemma__layoff Q R E J H32 H40).
------- destruct H41 as [V H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Cong G H3 G H3) as H45.
-------- apply (@euclidean__axioms.cn__congruencereflexive G H3).
-------- assert (* Cut *) (euclidean__defs.Lt G H3 G J) as H46.
--------- exists H3.
split.
---------- exact H6.
---------- exact H45.
--------- assert (* Cut *) (euclidean__defs.CongA D E F P Q R) as H47.
---------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric P Q R D E F H0).
---------- assert (* Cut *) (euclidean__defs.CongA D E F U Q V) as H48.
----------- apply (@lemma__equalangleshelper.lemma__equalangleshelper D E F P Q R U V H47 H18 H43).
----------- assert (* Cut *) (euclidean__defs.CongA U Q V D E F) as H49.
------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D E F U Q V H48).
------------ assert (* Cut *) (euclidean__defs.CongA U Q V G E J) as H50.
------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper U Q V D E F G J H49 H8 H10).
------------- assert (* Cut *) (euclidean__defs.CongA G E J U Q V) as H51.
-------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric U Q V G E J H50).
-------------- assert (* Cut *) (euclidean__axioms.Cong E G Q U) as H52.
--------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E Q U G H19).
--------------- assert (* Cut *) (euclidean__axioms.Cong E J Q V) as H53.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E Q V J H44).
---------------- assert (* Cut *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H54.
----------------- apply (@proposition__04.proposition__04 E G J Q U V H52 H53 H51).
----------------- assert (* Cut *) (euclidean__axioms.Cong U V G J) as H55.
------------------ destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric U G J V H55).
------------------ assert (* Cut *) (euclidean__axioms.neq G J) as H56.
------------------- destruct H54 as [H56 H57].
destruct H57 as [H58 H59].
assert (* Cut *) ((euclidean__axioms.neq H3 J) /\ ((euclidean__axioms.neq G H3) /\ (euclidean__axioms.neq G J))) as H60.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G H3 J H6).
-------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
------------------- assert (* Cut *) (exists W, (euclidean__axioms.BetS U W V) /\ (euclidean__axioms.Cong U W G H3)) as H57.
-------------------- destruct H54 as [H57 H58].
destruct H58 as [H59 H60].
apply (@proposition__03.proposition__03 G J G H3 U V H46 H55).
-------------------- destruct H57 as [W H58].
destruct H58 as [H59 H60].
destruct H54 as [H61 H62].
destruct H62 as [H63 H64].
assert (* Cut *) (H3 = H3) as H65.
--------------------- apply (@logic.eq__refl Point H3).
--------------------- assert (* Cut *) (euclidean__defs.Out E H3 H3) as H66.
---------------------- apply (@lemma__ray4.lemma__ray4 E H3 H3).
-----------------------right.
left.
exact H65.

----------------------- exact H28.
---------------------- assert (* Cut *) (euclidean__defs.CongA A B C G E H3) as H67.
----------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A B C D E H3 G H3 H11 H8 H66).
----------------------- assert (* Cut *) (euclidean__axioms.nCol G E H3) as H68.
------------------------ apply (@euclidean__tactics.nCol__notCol G E H3).
-------------------------apply (@euclidean__tactics.nCol__not__Col G E H3).
--------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC A B C G E H3 H67).


------------------------ assert (* Cut *) (euclidean__axioms.nCol G H3 E) as H69.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol E H3 G) /\ ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G))))) as H69.
-------------------------- apply (@lemma__NCorder.lemma__NCorder G E H3 H68).
-------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H76.
------------------------- assert (* Cut *) (euclidean__axioms.neq U V) as H70.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq W V) /\ ((euclidean__axioms.neq U W) /\ (euclidean__axioms.neq U V))) as H70.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal U W V H59).
--------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H74.
-------------------------- assert (* Cut *) (euclidean__defs.Out U V W) as H71.
--------------------------- apply (@lemma__ray4.lemma__ray4 U V W).
----------------------------left.
exact H59.

---------------------------- exact H70.
--------------------------- assert (* Cut *) (Q = Q) as H72.
---------------------------- apply (@logic.eq__refl Point Q).
---------------------------- assert (* Cut *) (E = E) as H73.
----------------------------- apply (@logic.eq__refl Point E).
----------------------------- assert (* Cut *) (euclidean__axioms.nCol U Q V) as H74.
------------------------------ apply (@euclidean__tactics.nCol__notCol U Q V).
-------------------------------apply (@euclidean__tactics.nCol__not__Col U Q V).
--------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC G E J U Q V H51).


------------------------------ assert (* Cut *) (euclidean__axioms.neq U Q) as H75.
------------------------------- assert (* Cut *) ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U)))))) as H75.
-------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct U Q V H74).
-------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H76.
------------------------------- assert (* Cut *) (euclidean__defs.Out U Q Q) as H76.
-------------------------------- apply (@lemma__ray4.lemma__ray4 U Q Q).
---------------------------------right.
left.
exact H72.

--------------------------------- exact H75.
-------------------------------- assert (* Cut *) (~(G = E)) as H77.
--------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col G H3 E) as H78.
---------------------------------- right.
left.
exact H77.
---------------------------------- apply (@euclidean__tactics.Col__nCol__False U Q V H74).
-----------------------------------apply (@euclidean__tactics.not__nCol__Col U Q V).
------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False G H3 E H69 H78).


--------------------------------- assert (* Cut *) (euclidean__defs.Out G E E) as H78.
---------------------------------- apply (@lemma__ray4.lemma__ray4 G E E).
-----------------------------------right.
left.
exact H73.

----------------------------------- exact H77.
---------------------------------- assert (* Cut *) (euclidean__defs.CongA E G J Q U W) as H79.
----------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper E G J Q U V Q W H63 H76 H71).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA Q U W E G J) as H80.
------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric E G J Q U W H79).
------------------------------------ assert (* Cut *) (euclidean__defs.Out G J H3) as H81.
------------------------------------- apply (@lemma__ray4.lemma__ray4 G J H3).
--------------------------------------left.
exact H6.

-------------------------------------- exact H56.
------------------------------------- assert (* Cut *) (euclidean__defs.CongA Q U W E G H3) as H82.
-------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper Q U W E G J E H3 H80 H78 H81).
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G H3 Q U W) as H83.
--------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric Q U W E G H3 H82).
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q U W) as H84.
---------------------------------------- apply (@euclidean__tactics.nCol__notCol Q U W).
-----------------------------------------apply (@euclidean__tactics.nCol__not__Col Q U W).
------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC E G H3 Q U W H83).


---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol U W Q) as H85.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol U Q W) /\ ((euclidean__axioms.nCol U W Q) /\ ((euclidean__axioms.nCol W Q U) /\ ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q))))) as H85.
------------------------------------------ apply (@lemma__NCorder.lemma__NCorder Q U W H84).
------------------------------------------ destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H88.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H3 G E) as H86.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol H3 E G) /\ ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G))))) as H86.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder G H3 E H69).
------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
exact H87.
------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col W U Q)) as H87.
------------------------------------------- intro H87.
assert (* Cut *) (euclidean__axioms.Col U W Q) as H88.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col Q W U) /\ ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W))))) as H88.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder W U Q H87).
--------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H89.
-------------------------------------------- apply (@euclidean__tactics.Col__nCol__False H3 G E H86).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col H3 G E).
----------------------------------------------intro H89.
apply (@euclidean__tactics.Col__nCol__False U W Q H85 H88).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G H3 U W) as H88.
-------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric G U W H3 H60).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G E U Q) as H89.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G E U Q) /\ ((euclidean__axioms.Cong G E Q U) /\ (euclidean__axioms.Cong E G U Q))) as H89.
---------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip E G Q U H52).
---------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H90.
--------------------------------------------- assert (euclidean__defs.CongA E G H3 Q U W) as H90 by exact H83.
assert (* Cut *) (euclidean__defs.CongA Q U W W U Q) as H91.
---------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA Q U W H84).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G H3 W U Q) as H92.
----------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive E G H3 Q U W W U Q H90 H91).
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H3 G E E G H3) as H93.
------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA H3 G E H86).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H3 G E W U Q) as H94.
------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive H3 G E E G H3 W U Q H93 H92).
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H95.
-------------------------------------------------- apply (@proposition__04.proposition__04 G H3 E U W Q H88 H89 H94).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C U Q W) as H96.
--------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C G E H3 U Q W H67 H99).
--------------------------------------------------- assert (* Cut *) (W = W) as H97.
---------------------------------------------------- destruct H95 as [H97 H98].
destruct H98 as [H99 H100].
apply (@logic.eq__refl Point W).
---------------------------------------------------- assert (* Cut *) (~(Q = W)) as H98.
----------------------------------------------------- intro H98.
assert (* Cut *) (euclidean__axioms.Col Q U W) as H99.
------------------------------------------------------ right.
left.
exact H98.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col W U Q) as H100.
------------------------------------------------------- destruct H95 as [H100 H101].
destruct H101 as [H102 H103].
assert (* Cut *) ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col W Q U) /\ ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q))))) as H104.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q U W H99).
-------------------------------------------------------- destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H112.
------------------------------------------------------- apply (@H87 H100).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q W W) as H99.
------------------------------------------------------ destruct H95 as [H99 H100].
destruct H100 as [H101 H102].
apply (@lemma__ray4.lemma__ray4 Q W W).
-------------------------------------------------------right.
left.
exact H97.

------------------------------------------------------- exact H98.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out Q U P) as H100.
------------------------------------------------------- destruct H95 as [H100 H101].
destruct H101 as [H102 H103].
apply (@lemma__ray5.lemma__ray5 Q P U H18).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C P Q W) as H101.
-------------------------------------------------------- destruct H95 as [H101 H102].
destruct H102 as [H103 H104].
apply (@lemma__equalangleshelper.lemma__equalangleshelper A B C U Q W P W H96 H100 H99).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C P Q R) as H102.
--------------------------------------------------------- exists U.
exists W.
exists V.
split.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H18.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H43.
------------------------------------------------------------ exact H101.
--------------------------------------------------------- exact H102.
Qed.
