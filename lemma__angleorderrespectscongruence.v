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
Definition lemma__angleorderrespectscongruence : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.LtA A B C D E F) -> ((euclidean__defs.CongA P Q R D E F) -> (euclidean__defs.LtA A B C P Q R)).
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
assert (* Cut *) (exists (G: euclidean__axioms.Point) (H1: euclidean__axioms.Point) (J: euclidean__axioms.Point), (euclidean__axioms.BetS G H1 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H1)))) as H1.
- exact H.
- assert (exists G: euclidean__axioms.Point, (exists (H2: euclidean__axioms.Point) (J: euclidean__axioms.Point), (euclidean__axioms.BetS G H2 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H2))))) as H2.
-- exact H1.
-- destruct H2 as [G H2].
assert (exists H3: euclidean__axioms.Point, (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS G H3 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H3))))) as H4.
--- exact H2.
--- destruct H4 as [H3 H4].
assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS G H3 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H3))))) as H5.
---- exact H4.
---- destruct H5 as [J H5].
assert (* AndElim *) ((euclidean__axioms.BetS G H3 J) /\ ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H3)))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Out E D G) /\ ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H3))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Out E F J) /\ (euclidean__defs.CongA A B C D E H3)) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
-------- split.
--------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
---------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H0).
---------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
exact H13.
--------- split.
---------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
----------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H0).
----------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
exact H15.
---------- split.
----------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
------------ apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H0).
------------ assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H17.
----------- split.
------------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H12.
------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H13.
-------------- exact H12.
-------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
exact H19.
------------ split.
------------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
-------------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H0).
-------------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
--------------- exact H12.
--------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
---------------- exact H14.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
exact H21.
------------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H12.
-------------- apply (@lemma__angledistinct.lemma__angledistinct (P) (Q) (R) (D) (E) (F) H0).
-------------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
--------------- exact H12.
--------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
---------------- exact H14.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
exact H22.
-------- assert (* Cut *) (euclidean__axioms.neq Q P) as H13.
--------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H19.
------------- exact H18.
------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H21.
-------------- exact H20.
-------------- destruct H21 as [H21 H22].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (Q) H13).
--------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H14.
---------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H14.
----------- exact H12.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
split.
---------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
----------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
----------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
-------------------- exact H28.
-------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
exact H25.
---------------- split.
----------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
------------------ apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
------------------ assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
--------------------- exact H28.
--------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
exact H27.
----------------- split.
------------------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
------------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
exact H29.
------------------ split.
------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
-------------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
---------------------- exact H26.
---------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
exact H20.
------------------- split.
-------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
--------------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
--------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H33.
-------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H24.
--------------------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (D) (E) (H3) H11).
--------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H34.
---------- assert (* Cut *) (euclidean__axioms.neq E G) as H15.
----------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H25.
----------------- exact H12.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H27.
------------------ exact H26.
------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H29.
------------------- exact H28.
------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H31.
-------------------- exact H30.
-------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H33.
--------------------- exact H32.
--------------------- destruct H33 as [H33 H34].
apply (@lemma__raystrict.lemma__raystrict (E) (D) (G) H8).
----------- assert (* Cut *) (exists (U: euclidean__axioms.Point), (euclidean__defs.Out Q P U) /\ (euclidean__axioms.Cong Q U E G)) as H16.
------------ assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H16.
------------- exact H14.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H26.
------------------ exact H12.
------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H28.
------------------- exact H27.
------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H30.
-------------------- exact H29.
-------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H32.
--------------------- exact H31.
--------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H34.
---------------------- exact H33.
---------------------- destruct H34 as [H34 H35].
apply (@lemma__layoff.lemma__layoff (Q) (P) (E) (G) (H13) H15).
------------ assert (exists U: euclidean__axioms.Point, ((euclidean__defs.Out Q P U) /\ (euclidean__axioms.Cong Q U E G))) as H17.
------------- exact H16.
------------- destruct H17 as [U H17].
assert (* AndElim *) ((euclidean__defs.Out Q P U) /\ (euclidean__axioms.Cong Q U E G)) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))))) as H20.
--------------- exact H14.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3))) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq E H3) /\ (euclidean__axioms.neq D H3)) as H28.
------------------- exact H27.
------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))))) as H30.
-------------------- exact H12.
-------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))))) as H32.
--------------------- exact H31.
--------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)))) as H34.
---------------------- exact H33.
---------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F))) as H36.
----------------------- exact H35.
----------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq D F)) as H38.
------------------------ exact H37.
------------------------ destruct H38 as [H38 H39].
assert (* Cut *) (euclidean__axioms.neq E J) as H40.
------------------------- apply (@lemma__raystrict.lemma__raystrict (E) (F) (J) H10).
------------------------- assert (* Cut *) (exists (V: euclidean__axioms.Point), (euclidean__defs.Out Q R V) /\ (euclidean__axioms.Cong Q V E J)) as H41.
-------------------------- apply (@lemma__layoff.lemma__layoff (Q) (R) (E) (J) (H32) H40).
-------------------------- assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Out Q R V) /\ (euclidean__axioms.Cong Q V E J))) as H42.
--------------------------- exact H41.
--------------------------- destruct H42 as [V H42].
assert (* AndElim *) ((euclidean__defs.Out Q R V) /\ (euclidean__axioms.Cong Q V E J)) as H43.
---------------------------- exact H42.
---------------------------- destruct H43 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Cong G H3 G H3) as H45.
----------------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) H3).
----------------------------- assert (* Cut *) (euclidean__defs.Lt G H3 G J) as H46.
------------------------------ exists H3.
split.
------------------------------- exact H6.
------------------------------- exact H45.
------------------------------ assert (* Cut *) (euclidean__defs.CongA D E F P Q R) as H47.
------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (Q) (R) (D) (E) (F) H0).
------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F U Q V) as H48.
-------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (E) (F) (P) (Q) (R) (U) (V) (H47) (H18) H43).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA U Q V D E F) as H49.
--------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (U) (Q) (V) H48).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA U Q V G E J) as H50.
---------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (U) (Q) (V) (D) (E) (F) (G) (J) (H49) (H8) H10).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA G E J U Q V) as H51.
----------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (U) (Q) (V) (G) (E) (J) H50).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong E G Q U) as H52.
------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (Q) (U) (G) H19).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E J Q V) as H53.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (Q) (V) (J) H44).
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H54.
-------------------------------------- apply (@proposition__04.proposition__04 (E) (G) (J) (Q) (U) (V) (H52) (H53) H51).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong U V G J) as H55.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H55.
---------------------------------------- exact H54.
---------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U)) as H57.
----------------------------------------- exact H56.
----------------------------------------- destruct H57 as [H57 H58].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (U) (G) (J) (V) H55).
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq G J) as H56.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H56.
----------------------------------------- exact H54.
----------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U)) as H58.
------------------------------------------ exact H57.
------------------------------------------ destruct H58 as [H58 H59].
assert (* Cut *) ((euclidean__axioms.neq H3 J) /\ ((euclidean__axioms.neq G H3) /\ (euclidean__axioms.neq G J))) as H60.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (H3) (J) H6).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H3 J) /\ ((euclidean__axioms.neq G H3) /\ (euclidean__axioms.neq G J))) as H61.
-------------------------------------------- exact H60.
-------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq G H3) /\ (euclidean__axioms.neq G J)) as H63.
--------------------------------------------- exact H62.
--------------------------------------------- destruct H63 as [H63 H64].
exact H64.
---------------------------------------- assert (* Cut *) (exists (W: euclidean__axioms.Point), (euclidean__axioms.BetS U W V) /\ (euclidean__axioms.Cong U W G H3)) as H57.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H57.
------------------------------------------ exact H54.
------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U)) as H59.
------------------------------------------- exact H58.
------------------------------------------- destruct H59 as [H59 H60].
apply (@proposition__03.proposition__03 (G) (J) (G) (H3) (U) (V) (H46) H55).
----------------------------------------- assert (exists W: euclidean__axioms.Point, ((euclidean__axioms.BetS U W V) /\ (euclidean__axioms.Cong U W G H3))) as H58.
------------------------------------------ exact H57.
------------------------------------------ destruct H58 as [W H58].
assert (* AndElim *) ((euclidean__axioms.BetS U W V) /\ (euclidean__axioms.Cong U W G H3)) as H59.
------------------------------------------- exact H58.
------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong G J U V) /\ ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U))) as H61.
-------------------------------------------- exact H54.
-------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA E G J Q U V) /\ (euclidean__defs.CongA E J G Q V U)) as H63.
--------------------------------------------- exact H62.
--------------------------------------------- destruct H63 as [H63 H64].
assert (* Cut *) (H3 = H3) as H65.
---------------------------------------------- apply (@logic.eq__refl (Point) H3).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out E H3 H3) as H66.
----------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (H3) (H3)).
------------------------------------------------right.
left.
exact H65.

------------------------------------------------ exact H28.
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C G E H3) as H67.
------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (D) (E) (H3) (G) (H3) (H11) (H8) H66).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol G E H3) as H68.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (G) (E) (H3)).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (G) (E) (H3)).
---------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (G) (E) (H3) H67).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H3 E) as H69.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol E H3 G) /\ ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G))))) as H69.
--------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (G) (E) (H3) H68).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol E H3 G) /\ ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G))))) as H70.
---------------------------------------------------- exact H69.
---------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.nCol E H3 G) /\ ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G)))) as H72.
----------------------------------------------------- exact H71.
----------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G))) as H74.
------------------------------------------------------ exact H73.
------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.nCol G H3 E) /\ (euclidean__axioms.nCol H3 E G)) as H76.
------------------------------------------------------- exact H75.
------------------------------------------------------- destruct H76 as [H76 H77].
exact H76.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq U V) as H70.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq W V) /\ ((euclidean__axioms.neq U W) /\ (euclidean__axioms.neq U V))) as H70.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (U) (W) (V) H59).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq W V) /\ ((euclidean__axioms.neq U W) /\ (euclidean__axioms.neq U V))) as H71.
----------------------------------------------------- exact H70.
----------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq U W) /\ (euclidean__axioms.neq U V)) as H73.
------------------------------------------------------ exact H72.
------------------------------------------------------ destruct H73 as [H73 H74].
exact H74.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out U V W) as H71.
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (U) (V) (W)).
-----------------------------------------------------left.
exact H59.

----------------------------------------------------- exact H70.
---------------------------------------------------- assert (* Cut *) (Q = Q) as H72.
----------------------------------------------------- apply (@logic.eq__refl (Point) Q).
----------------------------------------------------- assert (* Cut *) (E = E) as H73.
------------------------------------------------------ apply (@logic.eq__refl (Point) E).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol U Q V) as H74.
------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (U) (Q) (V)).
--------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (U) (Q) (V)).
---------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (E) (J) (U) (Q) (V) H51).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq U Q) as H75.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U)))))) as H75.
--------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (U) (Q) (V) H74).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq U Q) /\ ((euclidean__axioms.neq Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U)))))) as H76.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U))))) as H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U)))) as H80.
------------------------------------------------------------ exact H79.
------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq Q U) /\ ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U))) as H82.
------------------------------------------------------------- exact H81.
------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq V Q) /\ (euclidean__axioms.neq V U)) as H84.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- destruct H84 as [H84 H85].
exact H76.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out U Q Q) as H76.
--------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (U) (Q) (Q)).
----------------------------------------------------------right.
left.
exact H72.

---------------------------------------------------------- exact H75.
--------------------------------------------------------- assert (* Cut *) (~(G = E)) as H77.
---------------------------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col G H3 E) as H78.
----------------------------------------------------------- right.
left.
exact H77.
----------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (U) (Q) (V) (H74)).
------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (U) (Q) (V)).
-------------------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False (G) (H3) (E) (H69) H78).


---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G E E) as H78.
----------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (G) (E) (E)).
------------------------------------------------------------right.
left.
exact H73.

------------------------------------------------------------ exact H77.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G J Q U W) as H79.
------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (E) (G) (J) (Q) (U) (V) (Q) (W) (H63) (H76) H71).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA Q U W E G J) as H80.
------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (E) (G) (J) (Q) (U) (W) H79).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G J H3) as H81.
-------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (G) (J) (H3)).
---------------------------------------------------------------left.
exact H6.

--------------------------------------------------------------- exact H56.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA Q U W E G H3) as H82.
--------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (Q) (U) (W) (E) (G) (J) (E) (H3) (H80) (H78) H81).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G H3 Q U W) as H83.
---------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (Q) (U) (W) (E) (G) (H3) H82).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q U W) as H84.
----------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (Q) (U) (W)).
------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (Q) (U) (W)).
-------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (E) (G) (H3) (Q) (U) (W) H83).


----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol U W Q) as H85.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol U Q W) /\ ((euclidean__axioms.nCol U W Q) /\ ((euclidean__axioms.nCol W Q U) /\ ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q))))) as H85.
------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (Q) (U) (W) H84).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol U Q W) /\ ((euclidean__axioms.nCol U W Q) /\ ((euclidean__axioms.nCol W Q U) /\ ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q))))) as H86.
-------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.nCol U W Q) /\ ((euclidean__axioms.nCol W Q U) /\ ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q)))) as H88.
--------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.nCol W Q U) /\ ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q))) as H90.
---------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.nCol Q W U) /\ (euclidean__axioms.nCol W U Q)) as H92.
----------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------- destruct H92 as [H92 H93].
exact H88.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H3 G E) as H86.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol H3 E G) /\ ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G))))) as H86.
-------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (G) (H3) (E) H69).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H3 G E) /\ ((euclidean__axioms.nCol H3 E G) /\ ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G))))) as H87.
--------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.nCol H3 E G) /\ ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G)))) as H89.
---------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.nCol E G H3) /\ ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G))) as H91.
----------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.nCol G E H3) /\ (euclidean__axioms.nCol E H3 G)) as H93.
------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------ destruct H93 as [H93 H94].
exact H87.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col W U Q)) as H87.
-------------------------------------------------------------------- intro H87.
assert (* Cut *) (euclidean__axioms.Col U W Q) as H88.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col Q W U) /\ ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W))))) as H88.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (W) (U) (Q) H87).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col Q W U) /\ ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W))))) as H89.
----------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col Q W U) /\ ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W)))) as H91.
------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col Q W U) /\ ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W))) as H93.
------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col W Q U) /\ (euclidean__axioms.Col Q U W)) as H95.
-------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H89.
--------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (H3) (G) (E) (H86)).
----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (H3) (G) (E)).
-----------------------------------------------------------------------intro H89.
apply (@euclidean__tactics.Col__nCol__False (U) (W) (Q) (H85) H88).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G H3 U W) as H88.
--------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (G) (U) (W) (H3) H60).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G E U Q) as H89.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G E U Q) /\ ((euclidean__axioms.Cong G E Q U) /\ (euclidean__axioms.Cong E G U Q))) as H89.
----------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (G) (Q) (U) H52).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G E U Q) /\ ((euclidean__axioms.Cong G E Q U) /\ (euclidean__axioms.Cong E G U Q))) as H90.
------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------ destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Cong G E Q U) /\ (euclidean__axioms.Cong E G U Q)) as H92.
------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------- destruct H92 as [H92 H93].
exact H90.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E G H3 Q U W) as H90.
----------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA Q U W W U Q) as H91.
------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (Q) (U) (W) H84).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E G H3 W U Q) as H92.
------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (E) (G) (H3) (Q) (U) (W) (W) (U) (Q) (H90) H91).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H3 G E E G H3) as H93.
-------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H3) (G) (E) H86).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H3 G E W U Q) as H94.
--------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H3) (G) (E) (E) (G) (H3) (W) (U) (Q) (H93) H92).
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H95.
---------------------------------------------------------------------------- apply (@proposition__04.proposition__04 (G) (H3) (E) (U) (W) (Q) (H88) (H89) H94).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C U Q W) as H96.
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H96.
------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H98.
------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------- destruct H98 as [H98 H99].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (G) (E) (H3) (U) (Q) (W) (H67) H99).
----------------------------------------------------------------------------- assert (* Cut *) (W = W) as H97.
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H97.
------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H99.
-------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------- destruct H99 as [H99 H100].
apply (@logic.eq__refl (Point) W).
------------------------------------------------------------------------------ assert (* Cut *) (~(Q = W)) as H98.
------------------------------------------------------------------------------- intro H98.
assert (* Cut *) (euclidean__axioms.Col Q U W) as H99.
-------------------------------------------------------------------------------- right.
left.
exact H98.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col W U Q) as H100.
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H100.
---------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H102.
----------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* Cut *) ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col W Q U) /\ ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q))))) as H104.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (Q) (U) (W) H99).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col U Q W) /\ ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col W Q U) /\ ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q))))) as H105.
------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col U W Q) /\ ((euclidean__axioms.Col W Q U) /\ ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q)))) as H107.
-------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col W Q U) /\ ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q))) as H109.
--------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col Q W U) /\ (euclidean__axioms.Col W U Q)) as H111.
---------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H112.
--------------------------------------------------------------------------------- apply (@H87 H100).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q W W) as H99.
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H99.
--------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H101.
---------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------- destruct H101 as [H101 H102].
apply (@lemma__ray4.lemma__ray4 (Q) (W) (W)).
-----------------------------------------------------------------------------------right.
left.
exact H97.

----------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q U P) as H100.
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H100.
---------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H102.
----------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------- destruct H102 as [H102 H103].
apply (@lemma__ray5.lemma__ray5 (Q) (P) (U) H18).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C P Q W) as H101.
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H3 E W Q) /\ ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W))) as H101.
----------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__defs.CongA G H3 E U W Q) /\ (euclidean__defs.CongA G E H3 U Q W)) as H103.
------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------ destruct H103 as [H103 H104].
apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (U) (Q) (W) (P) (W) (H96) (H100) H99).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A B C P Q R) as H102.
----------------------------------------------------------------------------------- exists U.
exists W.
exists V.
split.
------------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H18.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------- exact H102.
Qed.
