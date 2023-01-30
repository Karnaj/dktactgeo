Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__9__5.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Require Export proposition__14.
Definition lemma__angleaddition : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point) (f: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point) (r: euclidean__axioms.Point), (euclidean__defs.SumA A B C D E F P Q R) -> ((euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.CongA D E F d e f) -> ((euclidean__defs.SumA a b c d e f p q r) -> (euclidean__defs.CongA P Q R p q r)))).
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
intro a.
intro b.
intro c.
intro d.
intro e.
intro f.
intro p.
intro q.
intro r.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__defs.CongA A B C P Q S) /\ ((euclidean__defs.CongA D E F S Q R) /\ (euclidean__axioms.BetS P S R))) as H3.
- exact H.
- assert (exists S: euclidean__axioms.Point, ((euclidean__defs.CongA A B C P Q S) /\ ((euclidean__defs.CongA D E F S Q R) /\ (euclidean__axioms.BetS P S R)))) as H4.
-- exact H3.
-- destruct H4 as [S H4].
assert (* AndElim *) ((euclidean__defs.CongA A B C P Q S) /\ ((euclidean__defs.CongA D E F S Q R) /\ (euclidean__axioms.BetS P S R))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.CongA D E F S Q R) /\ (euclidean__axioms.BetS P S R)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* Cut *) (exists (s: euclidean__axioms.Point), (euclidean__defs.CongA a b c p q s) /\ ((euclidean__defs.CongA d e f s q r) /\ (euclidean__axioms.BetS p s r))) as H9.
----- exact H2.
----- assert (exists s: euclidean__axioms.Point, ((euclidean__defs.CongA a b c p q s) /\ ((euclidean__defs.CongA d e f s q r) /\ (euclidean__axioms.BetS p s r)))) as H10.
------ exact H9.
------ destruct H10 as [s H10].
assert (* AndElim *) ((euclidean__defs.CongA a b c p q s) /\ ((euclidean__defs.CongA d e f s q r) /\ (euclidean__axioms.BetS p s r))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.CongA d e f s q r) /\ (euclidean__axioms.BetS p s r)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.nCol P Q S) as H15.
--------- apply (@euclidean__tactics.nCol__notCol (P) (Q) (S)).
----------apply (@euclidean__tactics.nCol__not__Col (P) (Q) (S)).
-----------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (P) (Q) (S) H5).


--------- assert (* Cut *) (euclidean__axioms.nCol S Q R) as H16.
---------- apply (@euclidean__tactics.nCol__notCol (S) (Q) (R)).
-----------apply (@euclidean__tactics.nCol__not__Col (S) (Q) (R)).
------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (S) (Q) (R) H7).


---------- assert (* Cut *) (euclidean__axioms.neq Q P) as H17.
----------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq P S) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P)))))) as H17.
------------ apply (@lemma__NCdistinct.lemma__NCdistinct (P) (Q) (S) H15).
------------ assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq P S) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P)))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq P S) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P))))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq P S) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P)))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P))) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P)) as H26.
----------------- exact H25.
----------------- destruct H26 as [H26 H27].
exact H24.
----------- assert (* Cut *) (euclidean__axioms.neq Q S) as H18.
------------ assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H18.
------------- apply (@lemma__NCdistinct.lemma__NCdistinct (S) (Q) (R) H16).
------------- assert (* AndElim *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)) as H27.
------------------ exact H26.
------------------ destruct H27 as [H27 H28].
exact H25.
------------ assert (* Cut *) (euclidean__axioms.neq Q R) as H19.
------------- assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H19.
-------------- apply (@lemma__NCdistinct.lemma__NCdistinct (S) (Q) (R) H16).
-------------- assert (* AndElim *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)) as H28.
------------------- exact H27.
------------------- destruct H28 as [H28 H29].
exact H22.
------------- assert (* Cut *) (euclidean__axioms.nCol p q s) as H20.
-------------- apply (@euclidean__tactics.nCol__notCol (p) (q) (s)).
---------------apply (@euclidean__tactics.nCol__not__Col (p) (q) (s)).
----------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (a) (b) (c) (p) (q) (s) H11).


-------------- assert (* Cut *) (euclidean__axioms.nCol s q r) as H21.
--------------- apply (@euclidean__tactics.nCol__notCol (s) (q) (r)).
----------------apply (@euclidean__tactics.nCol__not__Col (s) (q) (r)).
-----------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (d) (e) (f) (s) (q) (r) H13).


--------------- assert (* Cut *) (euclidean__axioms.neq q p) as H22.
---------------- assert (* Cut *) ((euclidean__axioms.neq p q) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq p s) /\ ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p)))))) as H22.
----------------- apply (@lemma__NCdistinct.lemma__NCdistinct (p) (q) (s) H20).
----------------- assert (* AndElim *) ((euclidean__axioms.neq p q) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq p s) /\ ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p)))))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq p s) /\ ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p))))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq p s) /\ ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p)))) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p))) as H29.
--------------------- exact H28.
--------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p)) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
exact H29.
---------------- assert (* Cut *) (euclidean__axioms.neq q r) as H23.
----------------- assert (* Cut *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H23.
------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (s) (q) (r) H21).
------------------ assert (* AndElim *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s))))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
exact H26.
----------------- assert (* Cut *) (euclidean__axioms.neq q s) as H24.
------------------ assert (* Cut *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H24.
------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (s) (q) (r) H21).
------------------- assert (* AndElim *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s))))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
exact H31.
------------------ assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__defs.Out q p G) /\ (euclidean__axioms.Cong q G Q P)) as H25.
------------------- apply (@lemma__layoff.lemma__layoff (q) (p) (Q) (P) (H22) H17).
------------------- assert (exists G: euclidean__axioms.Point, ((euclidean__defs.Out q p G) /\ (euclidean__axioms.Cong q G Q P))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [G H26].
assert (* AndElim *) ((euclidean__defs.Out q p G) /\ (euclidean__axioms.Cong q G Q P)) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* Cut *) (exists (H29: euclidean__axioms.Point), (euclidean__defs.Out q s H29) /\ (euclidean__axioms.Cong q H29 Q S)) as H29.
---------------------- apply (@lemma__layoff.lemma__layoff (q) (s) (Q) (S) (H24) H18).
---------------------- assert (exists H30: euclidean__axioms.Point, ((euclidean__defs.Out q s H30) /\ (euclidean__axioms.Cong q H30 Q S))) as H31.
----------------------- exact H29.
----------------------- destruct H31 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Out q s H30) /\ (euclidean__axioms.Cong q H30 Q S)) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [H32 H33].
assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__defs.Out q r K) /\ (euclidean__axioms.Cong q K Q R)) as H34.
------------------------- apply (@lemma__layoff.lemma__layoff (q) (r) (Q) (R) (H23) H19).
------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__defs.Out q r K) /\ (euclidean__axioms.Cong q K Q R))) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [K H35].
assert (* AndElim *) ((euclidean__defs.Out q r K) /\ (euclidean__axioms.Cong q K Q R)) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
assert (* Cut *) (euclidean__defs.CongA P Q S A B C) as H38.
---------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (P) (Q) (S) H5).
---------------------------- assert (* Cut *) (euclidean__defs.CongA P Q S a b c) as H39.
----------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (P) (Q) (S) (A) (B) (C) (a) (b) (c) (H38) H0).
----------------------------- assert (* Cut *) (euclidean__defs.CongA P Q S p q s) as H40.
------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (P) (Q) (S) (a) (b) (c) (p) (q) (s) (H39) H11).
------------------------------ assert (* Cut *) (euclidean__defs.CongA P Q S G q H30) as H41.
------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (P) (Q) (S) (p) (q) (s) (G) (H30) (H40) (H27) H32).
------------------------------- assert (* Cut *) (euclidean__defs.CongA S Q R D E F) as H42.
-------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (S) (Q) (R) H7).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA S Q R d e f) as H43.
--------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (S) (Q) (R) (D) (E) (F) (d) (e) (f) (H42) H1).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA S Q R s q r) as H44.
---------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (S) (Q) (R) (d) (e) (f) (s) (q) (r) (H43) H13).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA S Q R H30 q K) as H45.
----------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (S) (Q) (R) (s) (q) (r) (H30) (K) (H44) (H32) H36).
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol G q H30) as H46.
------------------------------------ apply (@euclidean__tactics.nCol__notCol (G) (q) (H30)).
-------------------------------------apply (@euclidean__tactics.nCol__not__Col (G) (q) (H30)).
--------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (P) (Q) (S) (G) (q) (H30) H41).


------------------------------------ assert (* Cut *) (euclidean__defs.CongA G q H30 P Q S) as H47.
------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (Q) (S) (G) (q) (H30) H41).
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H48.
-------------------------------------- apply (@proposition__04.proposition__04 (q) (G) (H30) (Q) (P) (S) (H28) (H33) H47).
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA H30 q K S Q R) as H49.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H51.
----------------------------------------- exact H50.
----------------------------------------- destruct H51 as [H51 H52].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (S) (Q) (R) (H30) (q) (K) H45).
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H50.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H50.
----------------------------------------- exact H48.
----------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H52.
------------------------------------------ exact H51.
------------------------------------------ destruct H52 as [H52 H53].
apply (@proposition__04.proposition__04 (q) (H30) (K) (Q) (S) (R) (H33) (H37) H49).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H30 q P S Q) as H51.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H51.
------------------------------------------ exact H50.
------------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H53.
------------------------------------------- exact H52.
------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H55.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H57.
--------------------------------------------- exact H56.
--------------------------------------------- destruct H57 as [H57 H58].
apply (@lemma__equalanglesflip.lemma__equalanglesflip (q) (H30) (G) (Q) (S) (P) H58).
----------------------------------------- assert (* Cut *) (Q = Q) as H52.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H52.
------------------------------------------- exact H50.
------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H54.
-------------------------------------------- exact H53.
-------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H56.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H58.
---------------------------------------------- exact H57.
---------------------------------------------- destruct H58 as [H58 H59].
apply (@logic.eq__refl (Point) Q).
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq S Q) as H53.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H53.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H57.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H59.
----------------------------------------------- exact H58.
----------------------------------------------- destruct H59 as [H59 H60].
assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H61.
------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (S) (Q) (R) H16).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H62.
------------------------------------------------- exact H61.
------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))))) as H64.
-------------------------------------------------- exact H63.
-------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))) as H66.
--------------------------------------------------- exact H65.
--------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S))) as H68.
---------------------------------------------------- exact H67.
---------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)) as H70.
----------------------------------------------------- exact H69.
----------------------------------------------------- destruct H70 as [H70 H71].
exact H62.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out S Q Q) as H54.
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H54.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H56.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H58.
----------------------------------------------- exact H48.
----------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H60.
------------------------------------------------ exact H59.
------------------------------------------------ destruct H60 as [H60 H61].
apply (@lemma__ray4.lemma__ray4 (S) (Q) (Q)).
-------------------------------------------------right.
left.
exact H52.

------------------------------------------------- exact H53.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Supp P S Q Q R) as H55.
--------------------------------------------- split.
---------------------------------------------- exact H54.
---------------------------------------------- exact H8.
--------------------------------------------- assert (* Cut *) (euclidean__defs.RT G H30 q q H30 K) as H56.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H56.
----------------------------------------------- exact H50.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as __TmpHyp.
------------------------------------------------ exact H56.
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H57.
------------------------------------------------- exact __TmpHyp.
------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H59.
-------------------------------------------------- exact H58.
-------------------------------------------------- destruct H59 as [H59 H60].
assert (* Cut *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H61.
--------------------------------------------------- exact H48.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as __TmpHyp0.
---------------------------------------------------- exact H61.
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H62.
----------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
exists P.
exists S.
exists R.
exists Q.
exists Q.
split.
------------------------------------------------------- exact H55.
------------------------------------------------------- split.
-------------------------------------------------------- exact H51.
-------------------------------------------------------- exact H59.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q s H30) as H57.
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H57.
------------------------------------------------ exact H50.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H61.
-------------------------------------------------- exact H48.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (q) (s) (H30) H32).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q H30 s) as H58.
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H58.
------------------------------------------------- exact H50.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H62.
--------------------------------------------------- exact H48.
--------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H64.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H64 as [H64 H65].
assert (* Cut *) ((euclidean__axioms.Col s q H30) /\ ((euclidean__axioms.Col s H30 q) /\ ((euclidean__axioms.Col H30 q s) /\ ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q))))) as H66.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (s) (H30) H57).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col s q H30) /\ ((euclidean__axioms.Col s H30 q) /\ ((euclidean__axioms.Col H30 q s) /\ ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q))))) as H67.
------------------------------------------------------ exact H66.
------------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col s H30 q) /\ ((euclidean__axioms.Col H30 q s) /\ ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q)))) as H69.
------------------------------------------------------- exact H68.
------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col H30 q s) /\ ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q))) as H71.
-------------------------------------------------------- exact H70.
-------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q)) as H73.
--------------------------------------------------------- exact H72.
--------------------------------------------------------- destruct H73 as [H73 H74].
exact H73.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col q p G) as H59.
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H59.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H61.
--------------------------------------------------- exact H60.
--------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H63.
---------------------------------------------------- exact H48.
---------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H65.
----------------------------------------------------- exact H64.
----------------------------------------------------- destruct H65 as [H65 H66].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (q) (p) (G) H27).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G q p) as H60.
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H60.
--------------------------------------------------- exact H50.
--------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H62.
---------------------------------------------------- exact H61.
---------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H64.
----------------------------------------------------- exact H48.
----------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H66.
------------------------------------------------------ exact H65.
------------------------------------------------------ destruct H66 as [H66 H67].
assert (* Cut *) ((euclidean__axioms.Col p q G) /\ ((euclidean__axioms.Col p G q) /\ ((euclidean__axioms.Col G q p) /\ ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q))))) as H68.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (p) (G) H59).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p q G) /\ ((euclidean__axioms.Col p G q) /\ ((euclidean__axioms.Col G q p) /\ ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q))))) as H69.
-------------------------------------------------------- exact H68.
-------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col p G q) /\ ((euclidean__axioms.Col G q p) /\ ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q)))) as H71.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col G q p) /\ ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q))) as H73.
---------------------------------------------------------- exact H72.
---------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q)) as H75.
----------------------------------------------------------- exact H74.
----------------------------------------------------------- destruct H75 as [H75 H76].
exact H73.
-------------------------------------------------- assert (* Cut *) (q = q) as H61.
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H61.
---------------------------------------------------- exact H50.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H65.
------------------------------------------------------ exact H48.
------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H67.
------------------------------------------------------- exact H66.
------------------------------------------------------- destruct H67 as [H67 H68].
apply (@logic.eq__refl (Point) q).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G q q) as H62.
---------------------------------------------------- right.
right.
left.
exact H61.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q p) as H63.
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H63.
------------------------------------------------------ exact H50.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H67.
-------------------------------------------------------- exact H48.
-------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H69.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- destruct H69 as [H69 H70].
exact H22.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq p q) as H64.
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H64.
------------------------------------------------------- exact H50.
------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H68.
--------------------------------------------------------- exact H48.
--------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H70.
---------------------------------------------------------- exact H69.
---------------------------------------------------------- destruct H70 as [H70 H71].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (q) (p) H63).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol p q H30) as H65.
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H65.
-------------------------------------------------------- exact H50.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H69.
---------------------------------------------------------- exact H48.
---------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H71.
----------------------------------------------------------- exact H70.
----------------------------------------------------------- destruct H71 as [H71 H72].
apply (@euclidean__tactics.nCol__notCol (p) (q) (H30)).
------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (p) (q) (H30)).
-------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (G) (q) (H30) (p) (q) (H46) (H60) (H62) H64).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q H30 p) as H66.
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H66.
--------------------------------------------------------- exact H50.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H70.
----------------------------------------------------------- exact H48.
----------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H72.
------------------------------------------------------------ exact H71.
------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* Cut *) ((euclidean__axioms.nCol q p H30) /\ ((euclidean__axioms.nCol q H30 p) /\ ((euclidean__axioms.nCol H30 p q) /\ ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p))))) as H74.
------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (p) (q) (H30) H65).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol q p H30) /\ ((euclidean__axioms.nCol q H30 p) /\ ((euclidean__axioms.nCol H30 p q) /\ ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p))))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol q H30 p) /\ ((euclidean__axioms.nCol H30 p q) /\ ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p)))) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.nCol H30 p q) /\ ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p))) as H79.
---------------------------------------------------------------- exact H78.
---------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p)) as H81.
----------------------------------------------------------------- exact H80.
----------------------------------------------------------------- destruct H81 as [H81 H82].
exact H77.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS p q H30 r) as H67.
--------------------------------------------------------- exists s.
split.
---------------------------------------------------------- exact H14.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H58.
----------------------------------------------------------- exact H66.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS r q H30 p) as H68.
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H68.
----------------------------------------------------------- exact H50.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H72.
------------------------------------------------------------- exact H48.
------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H74.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- destruct H74 as [H74 H75].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (q) (H30) (p) (r) H67).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q H30 q) as H69.
----------------------------------------------------------- right.
left.
exact H61.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out q K r) as H70.
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H70.
------------------------------------------------------------- exact H50.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H74.
--------------------------------------------------------------- exact H48.
--------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H76.
---------------------------------------------------------------- exact H75.
---------------------------------------------------------------- destruct H76 as [H76 H77].
apply (@lemma__ray5.lemma__ray5 (q) (r) (K) H36).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS K q H30 p) as H71.
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H71.
-------------------------------------------------------------- exact H50.
-------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H75.
---------------------------------------------------------------- exact H48.
---------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H77.
----------------------------------------------------------------- exact H76.
----------------------------------------------------------------- destruct H77 as [H77 H78].
apply (@lemma__9__5.lemma__9__5 (q) (H30) (p) (r) (K) (q) (H68) (H70) H69).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS p q H30 K) as H72.
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H72.
--------------------------------------------------------------- exact H50.
--------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H74.
---------------------------------------------------------------- exact H73.
---------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H76.
----------------------------------------------------------------- exact H48.
----------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H78.
------------------------------------------------------------------ exact H77.
------------------------------------------------------------------ destruct H78 as [H78 H79].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (q) (H30) (K) (p) H71).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out q G p) as H73.
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H73.
---------------------------------------------------------------- exact H50.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H77.
------------------------------------------------------------------ exact H48.
------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
apply (@lemma__ray5.lemma__ray5 (q) (p) (G) H27).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G q H30 K) as H74.
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H74.
----------------------------------------------------------------- exact H50.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H78.
------------------------------------------------------------------- exact H48.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
apply (@lemma__9__5.lemma__9__5 (q) (H30) (K) (p) (G) (q) (H72) (H73) H69).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS K q H30 G) as H75.
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H75.
------------------------------------------------------------------ exact H50.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H79.
-------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H81.
--------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (q) (H30) (G) (K) H74).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q H30) as H76.
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H76.
------------------------------------------------------------------- exact H50.
------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H78.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H80.
--------------------------------------------------------------------- exact H48.
--------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H82.
---------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------- destruct H82 as [H82 H83].
apply (@lemma__raystrict.lemma__raystrict (q) (s) (H30) H32).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H30 q) as H77.
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H77.
-------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H79.
--------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H81.
---------------------------------------------------------------------- exact H48.
---------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H83.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H83 as [H83 H84].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (q) (H30) H76).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H30 q q) as H78.
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H78.
--------------------------------------------------------------------- exact H50.
--------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H80.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H82.
----------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
apply (@lemma__ray4.lemma__ray4 (H30) (q) (q)).
-------------------------------------------------------------------------right.
left.
exact H61.

------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G H30 K) as H79.
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H79.
---------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H83.
------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point), (euclidean__defs.RT A0 B0 C0 D0 B0 E0) -> ((euclidean__defs.Out B0 C0 D0) -> ((euclidean__axioms.TS E0 D0 B0 A0) -> (euclidean__axioms.BetS A0 B0 E0)))) as H87.
-------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Supp A0 B0 C0 D0 E0) /\ (euclidean__axioms.BetS A0 B0 E0)) as __2.
--------------------------------------------------------------------------- apply (@proposition__14.proposition__14 (A0) (B0) (C0) (D0) (E0) (__) (__0) __1).
--------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __3.
-------------------------------------------------------------------------- apply (@H87 (G) (H30) (q) (q) (K) (H56) (H78) H75).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G K P R) as H80.
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H80.
----------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H82.
------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------ destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H84.
------------------------------------------------------------------------- exact H48.
------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H86.
-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- destruct H86 as [H86 H87].
apply (@euclidean__axioms.cn__sumofparts (G) (H30) (K) (P) (S) (R) (H84) (H80) (H79) H8).
---------------------------------------------------------------------- assert (* Cut *) (P = P) as H81.
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H81.
------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H85.
-------------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
apply (@logic.eq__refl (Point) P).
----------------------------------------------------------------------- assert (* Cut *) (R = R) as H82.
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H82.
------------------------------------------------------------------------- exact H50.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H86.
--------------------------------------------------------------------------- exact H48.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
apply (@logic.eq__refl (Point) R).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out Q P P) as H83.
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H83.
-------------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H85.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H87.
---------------------------------------------------------------------------- exact H48.
---------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H89.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- destruct H89 as [H89 H90].
apply (@lemma__ray4.lemma__ray4 (Q) (P) (P)).
------------------------------------------------------------------------------right.
left.
exact H81.

------------------------------------------------------------------------------ exact H17.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q R R) as H84.
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H84.
--------------------------------------------------------------------------- exact H50.
--------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H86.
---------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H88.
----------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H90.
------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------ destruct H90 as [H90 H91].
apply (@lemma__ray4.lemma__ray4 (Q) (R) (R)).
-------------------------------------------------------------------------------right.
left.
exact H82.

------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P S Q) as H85.
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H85.
---------------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H87.
----------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H89.
------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H91.
------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* Cut *) ((euclidean__axioms.nCol Q P S) /\ ((euclidean__axioms.nCol Q S P) /\ ((euclidean__axioms.nCol S P Q) /\ ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P))))) as H93.
-------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (P) (Q) (S) H15).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol Q P S) /\ ((euclidean__axioms.nCol Q S P) /\ ((euclidean__axioms.nCol S P Q) /\ ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P))))) as H94.
--------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.nCol Q S P) /\ ((euclidean__axioms.nCol S P Q) /\ ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P)))) as H96.
---------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.nCol S P Q) /\ ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P))) as H98.
----------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P)) as H100.
------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------ destruct H100 as [H100 H101].
exact H100.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P S R) as H86.
---------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H8.
---------------------------------------------------------------------------- assert (* Cut *) (P = P) as H87.
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H87.
------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H89.
------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H91.
-------------------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H93.
--------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------- destruct H93 as [H93 H94].
exact H81.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P S P) as H88.
------------------------------------------------------------------------------ right.
left.
exact H87.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq P R) as H89.
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H89.
-------------------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H91.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H93.
---------------------------------------------------------------------------------- exact H48.
---------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H95.
----------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* Cut *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq P S) /\ (euclidean__axioms.neq P R))) as H97.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (P) (S) (R) H8).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq P S) /\ (euclidean__axioms.neq P R))) as H98.
------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq P S) /\ (euclidean__axioms.neq P R)) as H100.
-------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H101.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P R Q) as H90.
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H90.
--------------------------------------------------------------------------------- exact H50.
--------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H94.
----------------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H96.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
apply (@euclidean__tactics.nCol__notCol (P) (R) (Q)).
-------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (P) (R) (Q)).
--------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (P) (S) (Q) (P) (R) (H85) (H88) (H86) H89).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P Q R) as H91.
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H91.
---------------------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H93.
----------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H95.
------------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H97.
------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* Cut *) ((euclidean__axioms.nCol R P Q) /\ ((euclidean__axioms.nCol R Q P) /\ ((euclidean__axioms.nCol Q P R) /\ ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P))))) as H99.
-------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (P) (R) (Q) H90).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol R P Q) /\ ((euclidean__axioms.nCol R Q P) /\ ((euclidean__axioms.nCol Q P R) /\ ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P))))) as H100.
--------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol R Q P) /\ ((euclidean__axioms.nCol Q P R) /\ ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P)))) as H102.
---------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.nCol Q P R) /\ ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P))) as H104.
----------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P)) as H106.
------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------ destruct H106 as [H106 H107].
exact H106.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q P q G) as H92.
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H92.
----------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H94.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H96.
------------------------------------------------------------------------------------- exact H48.
------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H98.
-------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (Q) (q) (G) (P) H28).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q R q K) as H93.
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H93.
------------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H95.
------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H97.
-------------------------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H99.
--------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (Q) (q) (K) (R) H37).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong P R G K) as H94.
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H94.
------------------------------------------------------------------------------------- exact H50.
------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S)) as H96.
-------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H98.
--------------------------------------------------------------------------------------- exact H48.
--------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P)) as H100.
---------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (P) (G) (K) (R) H80).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA P Q R p q r) as H95.
------------------------------------------------------------------------------------- exists P.
exists R.
exists G.
exists K.
split.
-------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------- exact H95.
Qed.
