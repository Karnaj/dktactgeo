Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__crossbar.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray2.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Definition lemma__angleordertransitive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.LtA A B C D E F) -> ((euclidean__defs.LtA D E F P Q R) -> (euclidean__defs.LtA A B C P Q R)).
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
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (W: euclidean__axioms.Point), (euclidean__axioms.BetS U W V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W)))) as H1.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q X)))) as H1.
-- exact H0.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q X)))) as __TmpHyp.
--- exact H1.
--- assert (exists U: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q X))))) as H2.
---- exact __TmpHyp.
---- destruct H2 as [x H2].
assert (exists X: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.BetS x X V) /\ ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q X))))) as H3.
----- exact H2.
----- destruct H3 as [x0 H3].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.BetS x x0 V) /\ ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q x0))))) as H4.
------ exact H3.
------ destruct H4 as [x1 H4].
assert (* AndElim *) ((euclidean__axioms.BetS x x0 x1) /\ ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R x1) /\ (euclidean__defs.CongA D E F P Q x0)))) as H5.
------- exact H4.
------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out Q P x) /\ ((euclidean__defs.Out Q R x1) /\ (euclidean__defs.CongA D E F P Q x0))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out Q R x1) /\ (euclidean__defs.CongA D E F P Q x0)) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out E D U) /\ ((euclidean__defs.Out E F V) /\ (euclidean__defs.CongA A B C D E X)))) as H11.
---------- exact H.
---------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out E D U) /\ ((euclidean__defs.Out E F V) /\ (euclidean__defs.CongA A B C D E X)))) as __TmpHyp0.
----------- exact H11.
----------- assert (exists U: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out E D U) /\ ((euclidean__defs.Out E F V) /\ (euclidean__defs.CongA A B C D E X))))) as H12.
------------ exact __TmpHyp0.
------------ destruct H12 as [x2 H12].
assert (exists X: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.BetS x2 X V) /\ ((euclidean__defs.Out E D x2) /\ ((euclidean__defs.Out E F V) /\ (euclidean__defs.CongA A B C D E X))))) as H13.
------------- exact H12.
------------- destruct H13 as [x3 H13].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.BetS x2 x3 V) /\ ((euclidean__defs.Out E D x2) /\ ((euclidean__defs.Out E F V) /\ (euclidean__defs.CongA A B C D E x3))))) as H14.
-------------- exact H13.
-------------- destruct H14 as [x4 H14].
assert (* AndElim *) ((euclidean__axioms.BetS x2 x3 x4) /\ ((euclidean__defs.Out E D x2) /\ ((euclidean__defs.Out E F x4) /\ (euclidean__defs.CongA A B C D E x3)))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Out E D x2) /\ ((euclidean__defs.Out E F x4) /\ (euclidean__defs.CongA A B C D E x3))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Out E F x4) /\ (euclidean__defs.CongA A B C D E x3)) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
exists x.
exists x1.
exists x0.
split.
------------------ exact H5.
------------------ split.
------------------- exact H7.
------------------- split.
-------------------- exact H9.
-------------------- exact H10.
- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (W: euclidean__axioms.Point), (euclidean__axioms.BetS U W V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W))))) as H2.
-- exact H1.
-- destruct H2 as [U H2].
assert (exists V: euclidean__axioms.Point, (exists (W: euclidean__axioms.Point), (euclidean__axioms.BetS U W V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W))))) as H3.
--- exact H2.
--- destruct H3 as [V H3].
assert (exists W: euclidean__axioms.Point, ((euclidean__axioms.BetS U W V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W))))) as H4.
---- exact H3.
---- destruct H4 as [W H4].
assert (* AndElim *) ((euclidean__axioms.BetS U W V) /\ ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W)))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out Q P U) /\ ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out Q R V) /\ (euclidean__defs.CongA D E F P Q W)) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__defs.CongA P Q W D E F) as H11.
-------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (P) (Q) (W) H10).
-------- assert (* Cut *) (euclidean__axioms.neq D E) as H12.
--------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
---------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (W) (D) (E) (F) H11).
---------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
exact H19.
--------- assert (* Cut *) (euclidean__axioms.neq E D) as H13.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H12).
---------- assert (* Cut *) (euclidean__axioms.neq E F) as H14.
----------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H14.
------------ apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (W) (D) (E) (F) H11).
------------ assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
exact H23.
----------- assert (* Cut *) (euclidean__axioms.neq Q U) as H15.
------------ apply (@lemma__raystrict.lemma__raystrict (Q) (P) (U) H7).
------------ assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__defs.Out E D G) /\ (euclidean__axioms.Cong E G Q U)) as H16.
------------- apply (@lemma__layoff.lemma__layoff (E) (D) (Q) (U) (H13) H15).
------------- assert (exists G: euclidean__axioms.Point, ((euclidean__defs.Out E D G) /\ (euclidean__axioms.Cong E G Q U))) as H17.
-------------- exact H16.
-------------- destruct H17 as [G H17].
assert (* AndElim *) ((euclidean__defs.Out E D G) /\ (euclidean__axioms.Cong E G Q U)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.neq Q W) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H20.
----------------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (W) (D) (E) (F) H11).
----------------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq Q W) /\ ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq P W) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
exact H23.
---------------- assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__defs.Out E F J) /\ (euclidean__axioms.Cong E J Q W)) as H21.
----------------- apply (@lemma__layoff.lemma__layoff (E) (F) (Q) (W) (H14) H20).
----------------- assert (exists J: euclidean__axioms.Point, ((euclidean__defs.Out E F J) /\ (euclidean__axioms.Cong E J Q W))) as H22.
------------------ exact H21.
------------------ destruct H22 as [J H22].
assert (* AndElim *) ((euclidean__defs.Out E F J) /\ (euclidean__axioms.Cong E J Q W)) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__axioms.nCol D E F) as H25.
-------------------- apply (@euclidean__tactics.nCol__notCol (D) (E) (F)).
---------------------apply (@euclidean__tactics.nCol__not__Col (D) (E) (F)).
----------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (P) (Q) (W) (D) (E) (F) H11).


-------------------- assert (* Cut *) (euclidean__defs.CongA D E F D E F) as H26.
--------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (D) (E) (F) H25).
--------------------- assert (* Cut *) (euclidean__defs.CongA D E F G E J) as H27.
---------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (D) (E) (F) (G) (J) (H26) (H18) H23).
---------------------- assert (* Cut *) (euclidean__defs.CongA G E J D E F) as H28.
----------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (G) (E) (J) H27).
----------------------- assert (* Cut *) (euclidean__defs.CongA G E J P Q W) as H29.
------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (E) (J) (D) (E) (F) (P) (Q) (W) (H28) H10).
------------------------ assert (* Cut *) (W = W) as H30.
------------------------- apply (@logic.eq__refl (Point) W).
------------------------- assert (* Cut *) (euclidean__defs.Out Q W W) as H31.
-------------------------- apply (@lemma__ray4.lemma__ray4 (Q) (W) (W)).
---------------------------right.
left.
exact H30.

--------------------------- exact H20.
-------------------------- assert (* Cut *) (euclidean__defs.CongA G E J U Q W) as H32.
--------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (G) (E) (J) (P) (Q) (W) (U) (W) (H29) (H7) H31).
--------------------------- assert (* Cut *) (euclidean__axioms.nCol G E J) as H33.
---------------------------- apply (@euclidean__tactics.nCol__notCol (G) (E) (J)).
-----------------------------apply (@euclidean__tactics.nCol__not__Col (G) (E) (J)).
------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (G) (E) (J) H27).


---------------------------- assert (* Cut *) (euclidean__axioms.nCol U Q W) as H34.
----------------------------- apply (@euclidean__tactics.nCol__notCol (U) (Q) (W)).
------------------------------apply (@euclidean__tactics.nCol__not__Col (U) (Q) (W)).
-------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (E) (J) (U) (Q) (W) H32).


----------------------------- assert (* Cut *) (euclidean__axioms.Triangle G E J) as H35.
------------------------------ exact H33.
------------------------------ assert (* Cut *) (euclidean__axioms.Triangle U Q W) as H36.
------------------------------- exact H34.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong G J U W) as H37.
-------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c) -> ((euclidean__defs.CongA B0 A0 C0 b a c) -> (euclidean__axioms.Cong B0 C0 b c)))) as H37.
--------------------------------- intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c) /\ ((euclidean__defs.CongA A0 B0 C0 a b c) /\ (euclidean__defs.CongA A0 C0 B0 a c b))) as __2.
---------------------------------- apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a) (b) (c) (__) (__0) __1).
---------------------------------- destruct __2 as [__2 __3].
exact __2.
--------------------------------- apply (@H37 (E) (G) (J) (Q) (U) (W) (H19) (H24) H32).
-------------------------------- assert (* Cut *) (W = W) as H38.
--------------------------------- exact H30.
--------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F U Q W) as H39.
---------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (P) (Q) (W) (U) (W) (H10) (H7) H31).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA U Q W D E F) as H40.
----------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (U) (Q) (W) H39).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F U Q W) as H41.
------------------------------------ exact H39.
------------------------------------ assert (* Cut *) (euclidean__defs.LtA A B C U Q W) as H42.
------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (D) (E) (F) (U) (Q) (W) (H) H40).
------------------------------------- assert (* Cut *) (exists (H43: euclidean__axioms.Point) (S: euclidean__axioms.Point) (T: euclidean__axioms.Point), (euclidean__axioms.BetS S H43 T) /\ ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H43)))) as H43.
-------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q U U0) /\ ((euclidean__defs.Out Q W V0) /\ (euclidean__defs.CongA A B C U Q X)))) as H43.
--------------------------------------- exact H42.
--------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q U U0) /\ ((euclidean__defs.Out Q W V0) /\ (euclidean__defs.CongA A B C U Q X)))) as __TmpHyp.
---------------------------------------- exact H43.
---------------------------------------- assert (exists U0: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q U U0) /\ ((euclidean__defs.Out Q W V0) /\ (euclidean__defs.CongA A B C U Q X))))) as H44.
----------------------------------------- exact __TmpHyp.
----------------------------------------- destruct H44 as [x H44].
assert (exists X: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point), (euclidean__axioms.BetS x X V0) /\ ((euclidean__defs.Out Q U x) /\ ((euclidean__defs.Out Q W V0) /\ (euclidean__defs.CongA A B C U Q X))))) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [x0 H45].
assert (exists V0: euclidean__axioms.Point, ((euclidean__axioms.BetS x x0 V0) /\ ((euclidean__defs.Out Q U x) /\ ((euclidean__defs.Out Q W V0) /\ (euclidean__defs.CongA A B C U Q x0))))) as H46.
------------------------------------------- exact H45.
------------------------------------------- destruct H46 as [x1 H46].
assert (* AndElim *) ((euclidean__axioms.BetS x x0 x1) /\ ((euclidean__defs.Out Q U x) /\ ((euclidean__defs.Out Q W x1) /\ (euclidean__defs.CongA A B C U Q x0)))) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Out Q U x) /\ ((euclidean__defs.Out Q W x1) /\ (euclidean__defs.CongA A B C U Q x0))) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Out Q W x1) /\ (euclidean__defs.CongA A B C U Q x0)) as H51.
---------------------------------------------- exact H50.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ (euclidean__defs.CongA D E F P Q X)))) as H53.
----------------------------------------------- exact H0.
----------------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ (euclidean__defs.CongA D E F P Q X)))) as __TmpHyp0.
------------------------------------------------ exact H53.
------------------------------------------------ assert (exists U0: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out Q P U0) /\ ((euclidean__defs.Out Q R V0) /\ (euclidean__defs.CongA D E F P Q X))))) as H54.
------------------------------------------------- exact __TmpHyp0.
------------------------------------------------- destruct H54 as [x2 H54].
assert (exists X: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point), (euclidean__axioms.BetS x2 X V0) /\ ((euclidean__defs.Out Q P x2) /\ ((euclidean__defs.Out Q R V0) /\ (euclidean__defs.CongA D E F P Q X))))) as H55.
-------------------------------------------------- exact H54.
-------------------------------------------------- destruct H55 as [x3 H55].
assert (exists V0: euclidean__axioms.Point, ((euclidean__axioms.BetS x2 x3 V0) /\ ((euclidean__defs.Out Q P x2) /\ ((euclidean__defs.Out Q R V0) /\ (euclidean__defs.CongA D E F P Q x3))))) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [x4 H56].
assert (* AndElim *) ((euclidean__axioms.BetS x2 x3 x4) /\ ((euclidean__defs.Out Q P x2) /\ ((euclidean__defs.Out Q R x4) /\ (euclidean__defs.CongA D E F P Q x3)))) as H57.
---------------------------------------------------- exact H56.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.Out Q P x2) /\ ((euclidean__defs.Out Q R x4) /\ (euclidean__defs.CongA D E F P Q x3))) as H59.
----------------------------------------------------- exact H58.
----------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.Out Q R x4) /\ (euclidean__defs.CongA D E F P Q x3)) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ (euclidean__defs.CongA A B C D E X)))) as H63.
------------------------------------------------------- exact H.
------------------------------------------------------- assert (* Cut *) (exists (U0: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ (euclidean__defs.CongA A B C D E X)))) as __TmpHyp1.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- assert (exists U0: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V0: euclidean__axioms.Point), (euclidean__axioms.BetS U0 X V0) /\ ((euclidean__defs.Out E D U0) /\ ((euclidean__defs.Out E F V0) /\ (euclidean__defs.CongA A B C D E X))))) as H64.
--------------------------------------------------------- exact __TmpHyp1.
--------------------------------------------------------- destruct H64 as [x5 H64].
assert (exists X: euclidean__axioms.Point, (exists (V0: euclidean__axioms.Point), (euclidean__axioms.BetS x5 X V0) /\ ((euclidean__defs.Out E D x5) /\ ((euclidean__defs.Out E F V0) /\ (euclidean__defs.CongA A B C D E X))))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [x6 H65].
assert (exists V0: euclidean__axioms.Point, ((euclidean__axioms.BetS x5 x6 V0) /\ ((euclidean__defs.Out E D x5) /\ ((euclidean__defs.Out E F V0) /\ (euclidean__defs.CongA A B C D E x6))))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [x7 H66].
assert (* AndElim *) ((euclidean__axioms.BetS x5 x6 x7) /\ ((euclidean__defs.Out E D x5) /\ ((euclidean__defs.Out E F x7) /\ (euclidean__defs.CongA A B C D E x6)))) as H67.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.Out E D x5) /\ ((euclidean__defs.Out E F x7) /\ (euclidean__defs.CongA A B C D E x6))) as H69.
------------------------------------------------------------- exact H68.
------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__defs.Out E F x7) /\ (euclidean__defs.CongA A B C D E x6)) as H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H71 as [H71 H72].
exists x0.
exists x.
exists x1.
split.
--------------------------------------------------------------- exact H47.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H49.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H51.
----------------------------------------------------------------- exact H52.
-------------------------------------- assert (exists H44: euclidean__axioms.Point, (exists (S: euclidean__axioms.Point) (T: euclidean__axioms.Point), (euclidean__axioms.BetS S H44 T) /\ ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44))))) as H45.
--------------------------------------- exact H43.
--------------------------------------- destruct H45 as [H44 H45].
assert (exists S: euclidean__axioms.Point, (exists (T: euclidean__axioms.Point), (euclidean__axioms.BetS S H44 T) /\ ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44))))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [S H46].
assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.BetS S H44 T) /\ ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44))))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [T H47].
assert (* AndElim *) ((euclidean__axioms.BetS S H44 T) /\ ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44)))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Out Q U S) /\ ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44))) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Out Q W T) /\ (euclidean__defs.CongA A B C U Q H44)) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
assert (* Cut *) (euclidean__defs.Out Q U P) as H54.
--------------------------------------------- apply (@lemma__ray5.lemma__ray5 (Q) (P) (U) H7).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q H44) as H55.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44)))))) as H55.
----------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (U) (Q) (H44) H53).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44)))))) as H56.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44))))) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44)))) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44))) as H62.
--------------------------------------------------- exact H61.
--------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq Q H44) /\ (euclidean__axioms.neq U H44)) as H64.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H64 as [H64 H65].
exact H64.
---------------------------------------------- assert (* Cut *) (H44 = H44) as H56.
----------------------------------------------- apply (@logic.eq__refl (Point) H44).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q H44 H44) as H57.
------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (Q) (H44) (H44)).
-------------------------------------------------right.
left.
exact H56.

------------------------------------------------- exact H55.
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C P Q H44) as H58.
------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (U) (Q) (H44) (P) (H44) (H53) (H54) H57).
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F P Q T) as H59.
-------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (U) (Q) (W) (P) (T) (H41) (H54) H52).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P Q T) as H60.
--------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (P) (Q) (T)).
----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (P) (Q) (T)).
-----------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (P) (Q) (T) H59).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle P Q T) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q P) as H62.
----------------------------------------------------- apply (@lemma__ray2.lemma__ray2 (Q) (P) (U) H7).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q T W) as H63.
------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 (Q) (W) (T) H52).
------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col S Q T)) as H64.
------------------------------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.Col Q U S) as H65.
-------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (Q) (U) (S) H50).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col U Q S) as H66.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col U Q S) /\ ((euclidean__axioms.Col U S Q) /\ ((euclidean__axioms.Col S Q U) /\ ((euclidean__axioms.Col Q S U) /\ (euclidean__axioms.Col S U Q))))) as H66.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (U) (S) H65).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col U Q S) /\ ((euclidean__axioms.Col U S Q) /\ ((euclidean__axioms.Col S Q U) /\ ((euclidean__axioms.Col Q S U) /\ (euclidean__axioms.Col S U Q))))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col U S Q) /\ ((euclidean__axioms.Col S Q U) /\ ((euclidean__axioms.Col Q S U) /\ (euclidean__axioms.Col S U Q)))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col S Q U) /\ ((euclidean__axioms.Col Q S U) /\ (euclidean__axioms.Col S U Q))) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col Q S U) /\ (euclidean__axioms.Col S U Q)) as H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- destruct H73 as [H73 H74].
exact H67.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q P U) as H67.
---------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (Q) (P) (U) H7).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col U Q P) as H68.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P U Q) /\ ((euclidean__axioms.Col U Q P) /\ ((euclidean__axioms.Col Q U P) /\ (euclidean__axioms.Col U P Q))))) as H68.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (Q) (P) (U) H67).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P U Q) /\ ((euclidean__axioms.Col U Q P) /\ ((euclidean__axioms.Col Q U P) /\ (euclidean__axioms.Col U P Q))))) as H69.
------------------------------------------------------------- exact H68.
------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col P U Q) /\ ((euclidean__axioms.Col U Q P) /\ ((euclidean__axioms.Col Q U P) /\ (euclidean__axioms.Col U P Q)))) as H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col U Q P) /\ ((euclidean__axioms.Col Q U P) /\ (euclidean__axioms.Col U P Q))) as H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col Q U P) /\ (euclidean__axioms.Col U P Q)) as H75.
---------------------------------------------------------------- exact H74.
---------------------------------------------------------------- destruct H75 as [H75 H76].
exact H73.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q U) as H69.
------------------------------------------------------------ exact H15.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq U Q) as H70.
------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (Q) (U) H69).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q S P) as H71.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (Q) (S) (P)).
---------------------------------------------------------------intro H71.
apply (@euclidean__tactics.Col__nCol__False (Q) (S) (P) (H71)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (U) (Q) (S) (P) (H66) (H68) H70).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S Q P) as H72.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col S Q P) /\ ((euclidean__axioms.Col S P Q) /\ ((euclidean__axioms.Col P Q S) /\ ((euclidean__axioms.Col Q P S) /\ (euclidean__axioms.Col P S Q))))) as H72.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (S) (P) H71).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col S Q P) /\ ((euclidean__axioms.Col S P Q) /\ ((euclidean__axioms.Col P Q S) /\ ((euclidean__axioms.Col Q P S) /\ (euclidean__axioms.Col P S Q))))) as H73.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col S P Q) /\ ((euclidean__axioms.Col P Q S) /\ ((euclidean__axioms.Col Q P S) /\ (euclidean__axioms.Col P S Q)))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col P Q S) /\ ((euclidean__axioms.Col Q P S) /\ (euclidean__axioms.Col P S Q))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col Q P S) /\ (euclidean__axioms.Col P S Q)) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H73.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q S) as H73.
---------------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (Q) (U) (S) H50).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq S Q) as H74.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (Q) (S) H73).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q T P) as H75.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (Q) (T) (P)).
-------------------------------------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False (Q) (T) (P) (H75)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (S) (Q) (T) (P) (H64) (H72) H74).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P Q T) as H76.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col T Q P) /\ ((euclidean__axioms.Col T P Q) /\ ((euclidean__axioms.Col P Q T) /\ ((euclidean__axioms.Col Q P T) /\ (euclidean__axioms.Col P T Q))))) as H76.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (T) (P) H75).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col T Q P) /\ ((euclidean__axioms.Col T P Q) /\ ((euclidean__axioms.Col P Q T) /\ ((euclidean__axioms.Col Q P T) /\ (euclidean__axioms.Col P T Q))))) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col T P Q) /\ ((euclidean__axioms.Col P Q T) /\ ((euclidean__axioms.Col Q P T) /\ (euclidean__axioms.Col P T Q)))) as H79.
---------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col P Q T) /\ ((euclidean__axioms.Col Q P T) /\ (euclidean__axioms.Col P T Q))) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col Q P T) /\ (euclidean__axioms.Col P T Q)) as H83.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
exact H81.
------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (P) (Q) (T) (H61) H76).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle S Q T) as H65.
-------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (S) (Q) (T) H64).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q S U) as H66.
--------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (Q) (U) (S) H50).
--------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__defs.Out Q H44 K) /\ (euclidean__axioms.BetS U K W)) as H67.
---------------------------------------------------------- apply (@lemma__crossbar.lemma__crossbar (S) (Q) (T) (H44) (U) (W) (H65) (H48) (H66) H63).
---------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__defs.Out Q H44 K) /\ (euclidean__axioms.BetS U K W))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [K H68].
assert (* AndElim *) ((euclidean__defs.Out Q H44 K) /\ (euclidean__axioms.BetS U K W)) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* Cut *) (euclidean__axioms.BetS U K V) as H71.
------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (U) (K) (W) (V) (H70) H5).
------------------------------------------------------------- assert (* Cut *) (P = P) as H72.
-------------------------------------------------------------- apply (@logic.eq__refl (Point) P).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q P P) as H73.
--------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (Q) (P) (P)).
----------------------------------------------------------------right.
left.
exact H72.

---------------------------------------------------------------- exact H62.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C P Q K) as H74.
---------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (P) (Q) (H44) (P) (K) (H58) (H73) H69).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C P Q R) as H75.
----------------------------------------------------------------- exists U.
exists K.
exists V.
split.
------------------------------------------------------------------ exact H71.
------------------------------------------------------------------ split.
------------------------------------------------------------------- exact H7.
------------------------------------------------------------------- split.
-------------------------------------------------------------------- exact H9.
-------------------------------------------------------------------- exact H74.
----------------------------------------------------------------- exact H75.
Qed.
