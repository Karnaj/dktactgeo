Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray1.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__16.
Definition proposition__27 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C F D) -> ((euclidean__defs.CongA A E F E F D) -> ((euclidean__axioms.TS A E F D) -> (euclidean__defs.Par A B C D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.neq A B) as H3.
- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H3.
-- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H).
-- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H4.
--- exact H3.
--- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H6.
---- exact H5.
---- destruct H6 as [H6 H7].
exact H7.
- assert (* Cut *) (euclidean__axioms.neq C D) as H4.
-- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H4.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (D) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D)) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
exact H8.
-- assert (* Cut *) (exists (H5: euclidean__axioms.Point), (euclidean__axioms.BetS A H5 D) /\ ((euclidean__axioms.Col E F H5) /\ (euclidean__axioms.nCol E F A))) as H5.
--- exact H2.
--- assert (exists H6: euclidean__axioms.Point, ((euclidean__axioms.BetS A H6 D) /\ ((euclidean__axioms.Col E F H6) /\ (euclidean__axioms.nCol E F A)))) as H7.
---- exact H5.
---- destruct H7 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS A H6 D) /\ ((euclidean__axioms.Col E F H6) /\ (euclidean__axioms.nCol E F A))) as H8.
----- exact H7.
----- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col E F H6) /\ (euclidean__axioms.nCol E F A)) as H10.
------ exact H9.
------ destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Col A E B) as H12.
------- right.
right.
right.
right.
left.
exact H.
------- assert (* Cut *) (euclidean__axioms.neq A E) as H13.
-------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H13.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H).
--------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
exact H16.
-------- assert (* Cut *) (euclidean__axioms.Col C F D) as H14.
--------- right.
right.
right.
right.
left.
exact H0.
--------- assert (* Cut *) (euclidean__axioms.neq F D) as H15.
---------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H15.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (D) H0).
----------- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D)) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
exact H16.
---------- assert (* Cut *) (euclidean__defs.CongA E F D A E F) as H16.
----------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (E) (F) (E) (F) (D) H1).
----------- assert (* Cut *) (euclidean__axioms.nCol E F D) as H17.
------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H17.
------------- exact H16.
------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp.
-------------- exact H17.
-------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H18.
--------------- exact __TmpHyp.
--------------- destruct H18 as [x H18].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong x V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H19.
---------------- exact H18.
---------------- destruct H19 as [x0 H19].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x) /\ ((euclidean__defs.Out F D x0) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x E u) /\ ((euclidean__axioms.Cong F x0 E v) /\ ((euclidean__axioms.Cong x x0 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [x1 H20].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x) /\ ((euclidean__defs.Out F D x0) /\ ((euclidean__defs.Out E A x1) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E v) /\ ((euclidean__axioms.Cong x x0 x1 v) /\ (euclidean__axioms.nCol E F D))))))))) as H21.
------------------ exact H20.
------------------ destruct H21 as [x2 H21].
assert (* AndElim *) ((euclidean__defs.Out F E x) /\ ((euclidean__defs.Out F D x0) /\ ((euclidean__defs.Out E A x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D)))))))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Out F D x0) /\ ((euclidean__defs.Out E A x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D))))))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Out E A x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D)))))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D))))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong F x E x1) /\ ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D)))) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong F x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D))) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol E F D)) as H34.
------------------------- exact H33.
------------------------- destruct H34 as [H34 H35].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H36.
-------------------------- exact H1.
-------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp0.
--------------------------- exact H36.
--------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H37.
---------------------------- exact __TmpHyp0.
---------------------------- destruct H37 as [x3 H37].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A x3) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x3 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x3 V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [x4 H38].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E A x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x3 F u) /\ ((euclidean__axioms.Cong E x4 F v) /\ ((euclidean__axioms.Cong x3 x4 u v) /\ (euclidean__axioms.nCol A E F))))))))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [x5 H39].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E A x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out F E x5) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F v) /\ ((euclidean__axioms.Cong x3 x4 x5 v) /\ (euclidean__axioms.nCol A E F))))))))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [x6 H40].
assert (* AndElim *) ((euclidean__defs.Out E A x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out F E x5) /\ ((euclidean__defs.Out F D x6) /\ ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F)))))))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out F E x5) /\ ((euclidean__defs.Out F D x6) /\ ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F))))))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Out F E x5) /\ ((euclidean__defs.Out F D x6) /\ ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F)))))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Out F D x6) /\ ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F))))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong E x3 F x5) /\ ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F)))) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Cong E x4 F x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F))) as H51.
------------------------------------- exact H50.
------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A E F)) as H53.
-------------------------------------- exact H52.
-------------------------------------- destruct H53 as [H53 H54].
exact H35.
------------ assert (* Cut *) (euclidean__axioms.neq E F) as H18.
------------- assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F)))))) as H18.
-------------- apply (@lemma__angledistinct.lemma__angledistinct (E) (F) (D) (A) (E) (F) H16).
-------------- assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F)))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F))))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F)))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F))) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F)) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
exact H27.
------------- assert (* Cut *) (euclidean__axioms.neq F E) as H19.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H18).
-------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H20.
--------------- intro H20.
assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G)))) as H21.
---------------- exact H20.
---------------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G))))) as H22.
----------------- exact H21.
----------------- destruct H22 as [G H22].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G)))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.Col B A G) as H29.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H29.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (G) H27).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)))) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))) as H34.
------------------------- exact H33.
------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A)) as H36.
-------------------------- exact H35.
-------------------------- destruct H36 as [H36 H37].
exact H30.
--------------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H30.
---------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H30.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H12).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H37.
--------------------------- exact H36.
--------------------------- destruct H37 as [H37 H38].
exact H35.
---------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H31.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H23).
----------------------- assert (* Cut *) (euclidean__axioms.Col A G E) as H32.
------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (G) (E)).
-------------------------intro H32.
apply (@euclidean__tactics.Col__nCol__False (A) (G) (E) (H32)).
--------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (G) (E) (H29) (H30) H31).


------------------------ assert (* Cut *) (euclidean__axioms.Col A E G) as H33.
------------------------- assert (* Cut *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H33.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (E) H32).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A)))) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A)) as H40.
------------------------------ exact H39.
------------------------------ destruct H40 as [H40 H41].
exact H40.
------------------------- assert (* Cut *) (F = F) as H34.
-------------------------- apply (@logic.eq__refl (Point) F).
-------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H35.
--------------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (F)).
----------------------------right.
left.
exact H34.

---------------------------- exact H18.
--------------------------- assert (* Cut *) (euclidean__defs.Supp A E F F B) as H36.
---------------------------- split.
----------------------------- exact H35.
----------------------------- exact H.
---------------------------- assert (* Cut *) (E = E) as H37.
----------------------------- apply (@logic.eq__refl (Point) E).
----------------------------- assert (* Cut *) (euclidean__defs.Out F E E) as H38.
------------------------------ apply (@lemma__ray4.lemma__ray4 (F) (E) (E)).
-------------------------------right.
left.
exact H37.

------------------------------- exact H19.
------------------------------ assert (* Cut *) (euclidean__axioms.BetS D F C) as H39.
------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (D) H0).
------------------------------- assert (* Cut *) (euclidean__defs.Supp D F E E C) as H40.
-------------------------------- split.
--------------------------------- exact H38.
--------------------------------- exact H39.
-------------------------------- assert (* Cut *) (euclidean__defs.CongA E F D D F E) as H41.
--------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (E) (F) (D) H17).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA A E F D F E) as H42.
---------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (E) (F) (E) (F) (D) (D) (F) (E) (H1) H41).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA F E B E F C) as H43.
----------------------------------- apply (@lemma__supplements.lemma__supplements (A) (E) (F) (F) (B) (D) (F) (E) (E) (C) (H42) (H36) H40).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA B E F C F E) as H44.
------------------------------------ apply (@lemma__equalanglesflip.lemma__equalanglesflip (F) (E) (B) (E) (F) (C) H43).
------------------------------------ assert (* Cut *) (~(euclidean__axioms.BetS A E G)) as H45.
------------------------------------- intro H45.
assert (* Cut *) (E = E) as H46.
-------------------------------------- exact H37.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F E) as H47.
--------------------------------------- right.
left.
exact H46.
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G E A) as H48.
---------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (G) H45).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F D) as H49.
----------------------------------------- exact H14.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H50.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H50.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H49).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [H57 H58].
exact H57.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H51.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G A))) as H51.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (E) (A) H48).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G A))) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G A)) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
exact H25.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G F) as H52.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (G) (F)).
---------------------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False (D) (G) (F) (H52)).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (G) (F) (H28) (H50) H51).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G F D) as H53.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H53.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (G) (F) H52).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H54.
----------------------------------------------- exact H53.
----------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D)))) as H56.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D)) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
exact H56.
--------------------------------------------- assert (* Cut *) (~(F = G)) as H54.
---------------------------------------------- intro H54.
assert (* Cut *) (euclidean__axioms.Col A E F) as H55.
----------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS C F0 D) -> ((euclidean__defs.CongA A E F0 E F0 D) -> ((euclidean__axioms.TS A E F0 D) -> ((euclidean__axioms.Col E F0 H6) -> ((euclidean__axioms.nCol E F0 A) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.neq F0 D) -> ((euclidean__defs.CongA E F0 D A E F0) -> ((euclidean__axioms.nCol E F0 D) -> ((euclidean__axioms.neq E F0) -> ((euclidean__axioms.neq F0 E) -> ((F0 = F0) -> ((euclidean__defs.Out E F0 F0) -> ((euclidean__defs.Supp A E F0 F0 B) -> ((euclidean__defs.Out F0 E E) -> ((euclidean__axioms.BetS D F0 C) -> ((euclidean__defs.Supp D F0 E E C) -> ((euclidean__defs.CongA E F0 D D F0 E) -> ((euclidean__defs.CongA A E F0 D F0 E) -> ((euclidean__defs.CongA F0 E B E F0 C) -> ((euclidean__defs.CongA B E F0 C F0 E) -> ((euclidean__axioms.Col E F0 E) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.Col C D F0) -> ((euclidean__axioms.Col D G F0) -> ((euclidean__axioms.Col G F0 D) -> (euclidean__axioms.Col A E F0)))))))))))))))))))))))))))) with (x := F).
------------------------------------------------intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
exact H33.

------------------------------------------------ exact H54.
------------------------------------------------ exact H0.
------------------------------------------------ exact H1.
------------------------------------------------ exact H2.
------------------------------------------------ exact H10.
------------------------------------------------ exact H11.
------------------------------------------------ exact H14.
------------------------------------------------ exact H15.
------------------------------------------------ exact H16.
------------------------------------------------ exact H17.
------------------------------------------------ exact H18.
------------------------------------------------ exact H19.
------------------------------------------------ exact H34.
------------------------------------------------ exact H35.
------------------------------------------------ exact H36.
------------------------------------------------ exact H38.
------------------------------------------------ exact H39.
------------------------------------------------ exact H40.
------------------------------------------------ exact H41.
------------------------------------------------ exact H42.
------------------------------------------------ exact H43.
------------------------------------------------ exact H44.
------------------------------------------------ exact H47.
------------------------------------------------ exact H49.
------------------------------------------------ exact H50.
------------------------------------------------ exact H52.
------------------------------------------------ exact H53.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H56.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H56.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (F) H55).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A)))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A)) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
exact H59.
------------------------------------------------ apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17)).
-------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (D)).
--------------------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (A) (H11) H56).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G F) as H55.
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (G) H54).
----------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E F G)) as H56.
------------------------------------------------ intro H56.
assert (* Cut *) (euclidean__axioms.Col G F E) as H57.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H57.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (G) H56).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
exact H65.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E D) as H58.
-------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (E) (D)).
---------------------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False (F) (E) (D) (H58)).
----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (F) (E) (D) (H57) (H53) H55).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H59.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F))))) as H59.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (E) (D) H58).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F))))) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F)))) as H62.
------------------------------------------------------ exact H61.
------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F))) as H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F)) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [H66 H67].
exact H60.
--------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H59).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS D H6 A) as H57.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (H6) (D) H8).
------------------------------------------------- assert (* Cut *) (euclidean__defs.OS D G E F) as H58.
-------------------------------------------------- exists A.
exists H6.
exists E.
split.
--------------------------------------------------- exact H10.
--------------------------------------------------- split.
---------------------------------------------------- exact H47.
---------------------------------------------------- split.
----------------------------------------------------- exact H57.
----------------------------------------------------- split.
------------------------------------------------------ exact H48.
------------------------------------------------------ split.
------------------------------------------------------- exact H17.
------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (F) (G) H56).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.OS G D E F) as H59.
--------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS G D E F) /\ ((euclidean__defs.OS D G F E) /\ (euclidean__defs.OS G D F E))) as H59.
---------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (F) (D) (G) H58).
---------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS G D E F) /\ ((euclidean__defs.OS D G F E) /\ (euclidean__defs.OS G D F E))) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.OS D G F E) /\ (euclidean__defs.OS G D F E)) as H62.
------------------------------------------------------ exact H61.
------------------------------------------------------ destruct H62 as [H62 H63].
exact H60.
--------------------------------------------------- assert (* Cut *) (F = F) as H60.
---------------------------------------------------- exact H34.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F F) as H61.
----------------------------------------------------- right.
right.
left.
exact H60.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D F C) as H62.
------------------------------------------------------ exact H39.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS D E F C) as H63.
------------------------------------------------------- exists F.
split.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- exact H17.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G E F C) as H64.
-------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (E) (F) (G) (D) (C) (H59) H63).
-------------------------------------------------------- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS G R C) /\ ((euclidean__axioms.Col E F R) /\ (euclidean__axioms.nCol E F G))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS G R C) /\ ((euclidean__axioms.Col E F R) /\ (euclidean__axioms.nCol E F G)))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [R H66].
assert (* AndElim *) ((euclidean__axioms.BetS G R C) /\ ((euclidean__axioms.Col E F R) /\ (euclidean__axioms.nCol E F G))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col E F R) /\ (euclidean__axioms.nCol E F G)) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* Cut *) (~(euclidean__axioms.neq F R)) as H71.
------------------------------------------------------------- intro H71.
assert (* Cut *) (euclidean__axioms.Col G R C) as H72.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H67.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G D) as H73.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H73.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (G) H28).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C)))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C)) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H80.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G R) as H74.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R G C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C G R) /\ ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G))))) as H74.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (R) (C) H72).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R G C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C G R) /\ ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G))))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C G R) /\ ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G)))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C G R) /\ ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G))) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G)) as H81.
--------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H79.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H75.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H75.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (G) (R) (C) H67).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H76.
------------------------------------------------------------------- exact H75.
------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C)) as H78.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- destruct H78 as [H78 H79].
exact H79.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H76.
------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (C) H75).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G C R) as H77.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H77.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (R) H74).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H78.
--------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C)))) as H80.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))) as H82.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C)) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
exact H78.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C D) as H78.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H78.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (D) H73).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H79.
---------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C)))) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))) as H83.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C)) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H79.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H79.
--------------------------------------------------------------------- exact H75.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq R F) as H80.
---------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (R) H71).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G R) as H81.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G))))) as H81.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (C) (D) H78).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G))))) as H82.
------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G)))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G)) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
exact H74.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H82.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H82.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (R) H81).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H83.
-------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C)))) as H85.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))) as H87.
---------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C)) as H89.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H50.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D F G) as H83.
------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (F) (G)).
--------------------------------------------------------------------------intro H83.
apply (@euclidean__tactics.Col__nCol__False (D) (F) (G) (H83)).
---------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (F) (G) (H82) (H28) H51).


------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F C) as H84.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H84.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (F) H82).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H85.
---------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)))) as H87.
----------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))) as H89.
------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)) as H91.
------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H87.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H85.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H85.
---------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (R) (C) H67).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H86.
----------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C)) as H88.
------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------ destruct H88 as [H88 H89].
exact H15.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H86.
---------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (D) H85).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F G C) as H87.
----------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (G) (C)).
------------------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (F) (G) (C) (H87)).
-------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (F) (G) (C) (H83) (H84) H86).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G F) as H88.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C F G) /\ ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F))))) as H88.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (G) (C) H87).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C F G) /\ ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F))))) as H89.
-------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C F G) /\ ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F)))) as H91.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col C F G) /\ ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F))) as H93.
---------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F)) as H95.
----------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H96.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C G D) as H89.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H89.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (F) H88).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H90.
--------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)))) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))) as H94.
----------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)) as H96.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
exact H73.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R F D) as H90.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (R) (F) (D)).
---------------------------------------------------------------------------------intro H90.
apply (@euclidean__tactics.Col__nCol__False (R) (F) (D) (H90)).
----------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (C) (G) (R) (F) (D) (H76) (H81) (H88) H89).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R F E) as H91.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E R) /\ ((euclidean__axioms.Col F R E) /\ ((euclidean__axioms.Col R E F) /\ ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E))))) as H91.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (R) H69).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E R) /\ ((euclidean__axioms.Col F R E) /\ ((euclidean__axioms.Col R E F) /\ ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E))))) as H92.
----------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col F R E) /\ ((euclidean__axioms.Col R E F) /\ ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E)))) as H94.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col R E F) /\ ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E))) as H96.
------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E)) as H98.
-------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H99.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H92.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (D) (E)).
-----------------------------------------------------------------------------------intro H92.
apply (@euclidean__tactics.Col__nCol__False (F) (D) (E) (H92)).
------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (R) (F) (D) (E) (H90) (H91) H80).


---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H93.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H93.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (D) (E) H92).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H94.
------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)))) as H96.
-------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))) as H98.
--------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)) as H100.
---------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H98.
----------------------------------------------------------------------------------- apply (@H56).
------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
-------------------------------------------------------------------------------------intro H94.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H93).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G F C) as H72.
-------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun X: euclidean__axioms.Point => euclidean__axioms.BetS G X C)) with (x := F).
--------------------------------------------------------------- exact H67.
---------------------------------------------------------------apply (@euclidean__tactics.NNPP (F = R) H71).

-------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E G F)) as H73.
--------------------------------------------------------------- intro H73.
assert (* Cut *) (euclidean__axioms.Col E F G) as H74.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H74.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (G) (F) H73).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E)))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E)) as H81.
--------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H81.
---------------------------------------------------------------- apply (@H56 H74).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle E G F) as H74.
---------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (G) (F) H73).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA G E F E F C) as H75.
----------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H75.
------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
------------------------------------------------------------------- apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
------------------------------------------------------------------ apply (@H75 (E) (G) (F) (C) (H74) H72).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA G E F F E B) as H76.
------------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (G) (E) (F) (E) (F) (C) (F) (E) (B) (H75) H43).
------------------------------------------------------------------ assert (* Cut *) (F = F) as H77.
------------------------------------------------------------------- exact H60.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H78.
-------------------------------------------------------------------- exact H35.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E G B) as H79.
--------------------------------------------------------------------- exists A.
split.
---------------------------------------------------------------------- exact H.
---------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col G E F)) as H80.
---------------------------------------------------------------------- intro H80.
assert (* Cut *) (euclidean__axioms.Col E G F) as H81.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E G F) /\ ((euclidean__axioms.Col E F G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G))))) as H81.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (E) (F) H80).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col E G F) /\ ((euclidean__axioms.Col E F G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G))))) as H82.
------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col E F G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G)))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G)) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
exact H82.
----------------------------------------------------------------------- apply (@H56).
------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
-------------------------------------------------------------------------intro H82.
apply (@H73 H81).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F G E F) as H81.
----------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (G) (E) (F)).
------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (G) (E) (F) H80).

----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F B E F) as H82.
------------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (G) (E) (F) (G) (E) (F) (B) (F) (H81) (H79) H78).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B E F) as H83.
------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as H83.
-------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as __TmpHyp.
--------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F))))))))) as H84.
---------------------------------------------------------------------------- exact __TmpHyp.
---------------------------------------------------------------------------- destruct H84 as [x H84].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G x) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong x V u v) /\ (euclidean__axioms.nCol G E F))))))))) as H85.
----------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------- destruct H85 as [x0 H85].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E G x) /\ ((euclidean__defs.Out E F x0) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x E u) /\ ((euclidean__axioms.Cong E x0 E v) /\ ((euclidean__axioms.Cong x x0 u v) /\ (euclidean__axioms.nCol G E F))))))))) as H86.
------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------ destruct H86 as [x1 H86].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E G x) /\ ((euclidean__defs.Out E F x0) /\ ((euclidean__defs.Out E B x1) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E v) /\ ((euclidean__axioms.Cong x x0 x1 v) /\ (euclidean__axioms.nCol G E F))))))))) as H87.
------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------- destruct H87 as [x2 H87].
assert (* AndElim *) ((euclidean__defs.Out E G x) /\ ((euclidean__defs.Out E F x0) /\ ((euclidean__defs.Out E B x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F)))))))) as H88.
-------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.Out E F x0) /\ ((euclidean__defs.Out E B x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F))))))) as H90.
--------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__defs.Out E B x1) /\ ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F)))))) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__defs.Out E F x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F))))) as H94.
----------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F)))) as H96.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F))) as H98.
------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol G E F)) as H100.
-------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as H102.
--------------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as __TmpHyp0.
---------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F))))))))) as H103.
----------------------------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------------------------- destruct H103 as [x3 H103].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E G x3) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x3 E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong x3 V u v) /\ (euclidean__axioms.nCol G E F))))))))) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [x4 H104].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E G x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x3 E u) /\ ((euclidean__axioms.Cong E x4 E v) /\ ((euclidean__axioms.Cong x3 x4 u v) /\ (euclidean__axioms.nCol G E F))))))))) as H105.
------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------- destruct H105 as [x5 H105].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E G x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out E G x5) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E v) /\ ((euclidean__axioms.Cong x3 x4 x5 v) /\ (euclidean__axioms.nCol G E F))))))))) as H106.
-------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------- destruct H106 as [x6 H106].
assert (* AndElim *) ((euclidean__defs.Out E G x3) /\ ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out E G x5) /\ ((euclidean__defs.Out E F x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F)))))))) as H107.
--------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.Out E F x4) /\ ((euclidean__defs.Out E G x5) /\ ((euclidean__defs.Out E F x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F))))))) as H109.
---------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__defs.Out E G x5) /\ ((euclidean__defs.Out E F x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F)))))) as H111.
----------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.Out E F x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F))))) as H113.
------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F)))) as H115.
------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F))) as H117.
-------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol G E F)) as H119.
--------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as H121.
---------------------------------------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F))))))))) as H122.
------------------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------------------ destruct H122 as [x7 H122].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B x7) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x7 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x7 V u v) /\ (euclidean__axioms.nCol B E F))))))))) as H123.
------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------- destruct H123 as [x8 H123].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E B x7) /\ ((euclidean__defs.Out E F x8) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x7 F u) /\ ((euclidean__axioms.Cong E x8 F v) /\ ((euclidean__axioms.Cong x7 x8 u v) /\ (euclidean__axioms.nCol B E F))))))))) as H124.
-------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------- destruct H124 as [x9 H124].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E B x7) /\ ((euclidean__defs.Out E F x8) /\ ((euclidean__defs.Out F C x9) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F v) /\ ((euclidean__axioms.Cong x7 x8 x9 v) /\ (euclidean__axioms.nCol B E F))))))))) as H125.
--------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------- destruct H125 as [x10 H125].
assert (* AndElim *) ((euclidean__defs.Out E B x7) /\ ((euclidean__defs.Out E F x8) /\ ((euclidean__defs.Out F C x9) /\ ((euclidean__defs.Out F E x10) /\ ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F)))))))) as H126.
---------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__defs.Out E F x8) /\ ((euclidean__defs.Out F C x9) /\ ((euclidean__defs.Out F E x10) /\ ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F))))))) as H128.
----------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__defs.Out F C x9) /\ ((euclidean__defs.Out F E x10) /\ ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F)))))) as H130.
------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__defs.Out F E x10) /\ ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F))))) as H132.
------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Cong E x7 F x9) /\ ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F)))) as H134.
-------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Cong E x8 F x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F))) as H136.
--------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol B E F)) as H138.
---------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as H140.
----------------------------------------------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B))))))))) as H141.
------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------------------------- destruct H141 as [x11 H141].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F x11) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x11 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x11 V u v) /\ (euclidean__axioms.nCol F E B))))))))) as H142.
-------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------- destruct H142 as [x12 H142].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E F x11) /\ ((euclidean__defs.Out E B x12) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x11 F u) /\ ((euclidean__axioms.Cong E x12 F v) /\ ((euclidean__axioms.Cong x11 x12 u v) /\ (euclidean__axioms.nCol F E B))))))))) as H143.
--------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------- destruct H143 as [x13 H143].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E F x11) /\ ((euclidean__defs.Out E B x12) /\ ((euclidean__defs.Out F E x13) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F v) /\ ((euclidean__axioms.Cong x11 x12 x13 v) /\ (euclidean__axioms.nCol F E B))))))))) as H144.
---------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------- destruct H144 as [x14 H144].
assert (* AndElim *) ((euclidean__defs.Out E F x11) /\ ((euclidean__defs.Out E B x12) /\ ((euclidean__defs.Out F E x13) /\ ((euclidean__defs.Out F C x14) /\ ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B)))))))) as H145.
----------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.Out E B x12) /\ ((euclidean__defs.Out F E x13) /\ ((euclidean__defs.Out F C x14) /\ ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B))))))) as H147.
------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------ destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.Out F E x13) /\ ((euclidean__defs.Out F C x14) /\ ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B)))))) as H149.
------------------------------------------------------------------------------------------------------------------------- exact H148.
------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__defs.Out F C x14) /\ ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B))))) as H151.
-------------------------------------------------------------------------------------------------------------------------- exact H150.
-------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.Cong E x11 F x13) /\ ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B)))) as H153.
--------------------------------------------------------------------------------------------------------------------------- exact H152.
--------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.Cong E x12 F x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B))) as H155.
---------------------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol F E B)) as H157.
----------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------- exact H159.
------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H160.
-------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x15 H160].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A x15) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x15 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x15 V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H161.
--------------------------------------------------------------------------------------------------------------------------------- exact H160.
--------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x16 H161].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E A x15) /\ ((euclidean__defs.Out E F x16) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x15 F u) /\ ((euclidean__axioms.Cong E x16 F v) /\ ((euclidean__axioms.Cong x15 x16 u v) /\ (euclidean__axioms.nCol A E F))))))))) as H162.
---------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x17 H162].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E A x15) /\ ((euclidean__defs.Out E F x16) /\ ((euclidean__defs.Out F D x17) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F v) /\ ((euclidean__axioms.Cong x15 x16 x17 v) /\ (euclidean__axioms.nCol A E F))))))))) as H163.
----------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [x18 H163].
assert (* AndElim *) ((euclidean__defs.Out E A x15) /\ ((euclidean__defs.Out E F x16) /\ ((euclidean__defs.Out F D x17) /\ ((euclidean__defs.Out F E x18) /\ ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F)))))))) as H164.
------------------------------------------------------------------------------------------------------------------------------------ exact H163.
------------------------------------------------------------------------------------------------------------------------------------ destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__defs.Out E F x16) /\ ((euclidean__defs.Out F D x17) /\ ((euclidean__defs.Out F E x18) /\ ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F))))))) as H166.
------------------------------------------------------------------------------------------------------------------------------------- exact H165.
------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__defs.Out F D x17) /\ ((euclidean__defs.Out F E x18) /\ ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F)))))) as H168.
-------------------------------------------------------------------------------------------------------------------------------------- exact H167.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__defs.Out F E x18) /\ ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F))))) as H170.
--------------------------------------------------------------------------------------------------------------------------------------- exact H169.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.Cong E x15 F x17) /\ ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F)))) as H172.
---------------------------------------------------------------------------------------------------------------------------------------- exact H171.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.Cong E x16 F x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F))) as H174.
----------------------------------------------------------------------------------------------------------------------------------------- exact H173.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol A E F)) as H176.
------------------------------------------------------------------------------------------------------------------------------------------ exact H175.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H176 as [H176 H177].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H178.
------------------------------------------------------------------------------------------------------------------------------------------- exact H41.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [x19 H179].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x19) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x19 F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong x19 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [x20 H180].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x19) /\ ((euclidean__defs.Out F D x20) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x19 F u) /\ ((euclidean__axioms.Cong F x20 F v) /\ ((euclidean__axioms.Cong x19 x20 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H181.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [x21 H181].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x19) /\ ((euclidean__defs.Out F D x20) /\ ((euclidean__defs.Out F D x21) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F v) /\ ((euclidean__axioms.Cong x19 x20 x21 v) /\ (euclidean__axioms.nCol E F D))))))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H181.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H182 as [x22 H182].
assert (* AndElim *) ((euclidean__defs.Out F E x19) /\ ((euclidean__defs.Out F D x20) /\ ((euclidean__defs.Out F D x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D)))))))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__defs.Out F D x20) /\ ((euclidean__defs.Out F D x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D))))))) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__defs.Out F D x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D)))))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D))))) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.Cong F x19 F x21) /\ ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D)))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.Cong F x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol E F D)) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp5.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H198.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [x23 H198].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x23) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x23 E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong x23 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [x24 H199].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x23) /\ ((euclidean__defs.Out F D x24) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x23 E u) /\ ((euclidean__axioms.Cong F x24 E v) /\ ((euclidean__axioms.Cong x23 x24 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H199.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H200 as [x25 H200].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x23) /\ ((euclidean__defs.Out F D x24) /\ ((euclidean__defs.Out E A x25) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E v) /\ ((euclidean__axioms.Cong x23 x24 x25 v) /\ (euclidean__axioms.nCol E F D))))))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [x26 H201].
assert (* AndElim *) ((euclidean__defs.Out F E x23) /\ ((euclidean__defs.Out F D x24) /\ ((euclidean__defs.Out E A x25) /\ ((euclidean__defs.Out E F x26) /\ ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D)))))))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__defs.Out F D x24) /\ ((euclidean__defs.Out E A x25) /\ ((euclidean__defs.Out E F x26) /\ ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D))))))) as H204.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__defs.Out E A x25) /\ ((euclidean__defs.Out E F x26) /\ ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D)))))) as H206.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__defs.Out E F x26) /\ ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D))))) as H208.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.Cong F x23 E x25) /\ ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D)))) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.Cong F x24 E x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol E F D)) as H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp6.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [x27 H217].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x27 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x27 V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H217.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H218 as [x28 H218].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x27 F u) /\ ((euclidean__axioms.Cong E x28 F v) /\ ((euclidean__axioms.Cong x27 x28 u v) /\ (euclidean__axioms.nCol A E F))))))))) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [x29 H219].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F E x29) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F v) /\ ((euclidean__axioms.Cong x27 x28 x29 v) /\ (euclidean__axioms.nCol A E F))))))))) as H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [x30 H220].
assert (* AndElim *) ((euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F E x29) /\ ((euclidean__defs.Out F D x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))))))) as H221.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F E x29) /\ ((euclidean__defs.Out F D x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))))))) as H223.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__defs.Out F E x29) /\ ((euclidean__defs.Out F D x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))))) as H225.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__defs.Out F D x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))))) as H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))) as H229.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))) as H231.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)) as H233.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
exact H139.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E F F E B) as H84.
-------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (E) (F) H83).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F F E B) as H85.
--------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (E) (F) (B) (E) (F) (F) (E) (B) (H82) H84).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E B G E F) as H86.
---------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (G) (E) (F) (F) (E) (B) H85).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA F E B F E B) as H87.
----------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (G) (E) (F) (F) (E) (B) (F) (E) (B) (H76) H86).
----------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA F E B F E B)) as H88.
------------------------------------------------------------------------------ apply (@lemma__angletrichotomy.lemma__angletrichotomy (F) (E) (B) (F) (E) (B) H87).
------------------------------------------------------------------------------ apply (@H56).
-------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
--------------------------------------------------------------------------------intro H89.
apply (@H88 H87).


------------------------------------- assert (* Cut *) (~(euclidean__defs.Out E A G)) as H46.
-------------------------------------- intro H46.
assert (* Cut *) (F = F) as H47.
--------------------------------------- exact H34.
--------------------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H48.
---------------------------------------- exact H35.
---------------------------------------- assert (* Cut *) (euclidean__defs.Out E G A) as H49.
----------------------------------------- apply (@lemma__ray5.lemma__ray5 (E) (A) (G) H46).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA E F D A E F) as H50.
------------------------------------------ exact H16.
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E F D G E F) as H51.
------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (E) (F) (D) (A) (E) (F) (G) (F) (H50) (H46) H48).
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E A) as H52.
-------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (B) H).
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as H53.
--------------------------------------------- apply (@lemma__ray1.lemma__ray1 (E) (G) (A) H49).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H54.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as H54.
----------------------------------------------- exact H53.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as __TmpHyp.
------------------------------------------------ exact H54.
------------------------------------------------ assert (euclidean__axioms.BetS E A G \/ (G = A) \/ (euclidean__axioms.BetS E G A)) as H55.
------------------------------------------------- exact __TmpHyp.
------------------------------------------------- destruct H55 as [H55|H55].
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H56.
--------------------------------------------------- apply (@lemma__3__7b.lemma__3__7b (B) (E) (A) (G) (H52) H55).
--------------------------------------------------- exact H56.
-------------------------------------------------- assert (G = A \/ euclidean__axioms.BetS E G A) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56|H56].
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H57.
----------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun G0: euclidean__axioms.Point => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Col C D G0) -> ((euclidean__axioms.Col B A G0) -> ((euclidean__axioms.Col A G0 E) -> ((euclidean__axioms.Col A E G0) -> ((~(euclidean__axioms.BetS A E G0)) -> ((euclidean__defs.Out E A G0) -> ((euclidean__defs.Out E G0 A) -> ((euclidean__defs.CongA E F D G0 E F) -> (euclidean__axioms.BetS B E G0))))))))))) with (x := G).
------------------------------------------------------intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
exact H52.

------------------------------------------------------ exact H56.
------------------------------------------------------ exact H27.
------------------------------------------------------ exact H28.
------------------------------------------------------ exact H29.
------------------------------------------------------ exact H32.
------------------------------------------------------ exact H33.
------------------------------------------------------ exact H45.
------------------------------------------------------ exact H46.
------------------------------------------------------ exact H49.
------------------------------------------------------ exact H51.
----------------------------------------------------- exact H57.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H57.
----------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (B) (E) (G) (A) (H52) H56).
----------------------------------------------------- exact H57.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G E B) as H55.
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (E) (G) H54).
----------------------------------------------- assert (* Cut *) (E = E) as H56.
------------------------------------------------ exact H37.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E F E) as H57.
------------------------------------------------- right.
left.
exact H56.
------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E F G)) as H58.
-------------------------------------------------- intro H58.
assert (* Cut *) (euclidean__axioms.Col B A G) as H59.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H59.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (G) H58).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)))) as H62.
------------------------------------------------------ exact H61.
------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))) as H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [H66 H67].
exact H29.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E B) as H60.
---------------------------------------------------- exact H12.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H61.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H61.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H60).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
exact H66.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G E) as H62.
------------------------------------------------------ exact H32.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G E A) as H63.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H63.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (E) H62).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H64.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A)))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A)) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
exact H66.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G E F) as H64.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H64.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (G) H58).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E)) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
exact H69.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E G) as H65.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B G))) as H65.
---------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (G) H54).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B G))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B G)) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
exact H66.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G E) as H66.
---------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (G) H65).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A F) as H67.
----------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (A) (F)).
------------------------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False (E) (A) (F) (H67)).
-------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (E) (A) (F) (H63) (H64) H66).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H68.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H68.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (F) H67).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E)))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E)) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
exact H75.
------------------------------------------------------------ apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17)).
-------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (D)).
--------------------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (A) (H11) H68).


-------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A G E F) as H59.
--------------------------------------------------- exists B.
exists E.
exists E.
split.
---------------------------------------------------- exact H57.
---------------------------------------------------- split.
----------------------------------------------------- exact H57.
----------------------------------------------------- split.
------------------------------------------------------ exact H.
------------------------------------------------------ split.
------------------------------------------------------- exact H55.
------------------------------------------------------- split.
-------------------------------------------------------- exact H11.
-------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (F) (G) H58).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.OS G A E F) as H60.
---------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS G A E F) /\ ((euclidean__defs.OS A G F E) /\ (euclidean__defs.OS G A F E))) as H60.
----------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (F) (A) (G) H59).
----------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS G A E F) /\ ((euclidean__defs.OS A G F E) /\ (euclidean__defs.OS G A F E))) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.OS A G F E) /\ (euclidean__defs.OS G A F E)) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
exact H61.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G E F D) as H61.
----------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (E) (F) (G) (A) (D) (H60) H2).
----------------------------------------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS G P D) /\ ((euclidean__axioms.Col E F P) /\ (euclidean__axioms.nCol E F G))) as H62.
------------------------------------------------------ exact H61.
------------------------------------------------------ assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS G P D) /\ ((euclidean__axioms.Col E F P) /\ (euclidean__axioms.nCol E F G)))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [P H63].
assert (* AndElim *) ((euclidean__axioms.BetS G P D) /\ ((euclidean__axioms.Col E F P) /\ (euclidean__axioms.nCol E F G))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col E F P) /\ (euclidean__axioms.nCol E F G)) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* Cut *) (euclidean__axioms.Col G P D) as H68.
---------------------------------------------------------- right.
right.
right.
right.
left.
exact H64.
---------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq P F)) as H69.
----------------------------------------------------------- intro H69.
assert (* Cut *) (euclidean__axioms.neq G D) as H70.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq P D) /\ ((euclidean__axioms.neq G P) /\ (euclidean__axioms.neq G D))) as H70.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (P) (D) H64).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq P D) /\ ((euclidean__axioms.neq G P) /\ (euclidean__axioms.neq G D))) as H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq G P) /\ (euclidean__axioms.neq G D)) as H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H73 as [H73 H74].
exact H74.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G D P) as H71.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P G D) /\ ((euclidean__axioms.Col P D G) /\ ((euclidean__axioms.Col D G P) /\ ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G))))) as H71.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (P) (D) H68).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col P G D) /\ ((euclidean__axioms.Col P D G) /\ ((euclidean__axioms.Col D G P) /\ ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G))))) as H72.
--------------------------------------------------------------- exact H71.
--------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col P D G) /\ ((euclidean__axioms.Col D G P) /\ ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G)))) as H74.
---------------------------------------------------------------- exact H73.
---------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col D G P) /\ ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G))) as H76.
----------------------------------------------------------------- exact H75.
----------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G)) as H78.
------------------------------------------------------------------ exact H77.
------------------------------------------------------------------ destruct H78 as [H78 H79].
exact H78.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F D) as H72.
-------------------------------------------------------------- exact H14.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H73.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H73.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H72).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H80.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G F) as H74.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (G) (F)).
-----------------------------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False (D) (G) (F) (H74)).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (G) (F) (H28) (H73) H25).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D F) as H75.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H75.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (G) (F) H74).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H76.
------------------------------------------------------------------- exact H75.
------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D)))) as H78.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))) as H80.
--------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D)) as H82.
---------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H76.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D P F) as H76.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (D) (P) (F)).
-------------------------------------------------------------------intro H76.
apply (@euclidean__tactics.Col__nCol__False (D) (P) (F) (H76)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (D) (P) (F) (H71) (H75) H70).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P F D) as H77.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P D F) /\ ((euclidean__axioms.Col P F D) /\ ((euclidean__axioms.Col F D P) /\ ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D))))) as H77.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (P) (F) H76).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col P D F) /\ ((euclidean__axioms.Col P F D) /\ ((euclidean__axioms.Col F D P) /\ ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D))))) as H78.
--------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col P F D) /\ ((euclidean__axioms.Col F D P) /\ ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D)))) as H80.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col F D P) /\ ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D))) as H82.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D)) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
exact H80.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P F E) as H78.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E P) /\ ((euclidean__axioms.Col F P E) /\ ((euclidean__axioms.Col P E F) /\ ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E))))) as H78.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (P) H66).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E P) /\ ((euclidean__axioms.Col F P E) /\ ((euclidean__axioms.Col P E F) /\ ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E))))) as H79.
---------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col F P E) /\ ((euclidean__axioms.Col P E F) /\ ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E)))) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col P E F) /\ ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E))) as H83.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E)) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H86.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H79.
--------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (D) (E)).
----------------------------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False (F) (D) (E) (H79)).
-----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (F) (D) (E) (H77) (H78) H69).


--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F D E)) as H80.
---------------------------------------------------------------------- intro H80.
assert (* Cut *) (euclidean__axioms.Col E F D) as H81.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H81.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (D) (E) H80).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H82.
------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
exact H86.
----------------------------------------------------------------------- apply (@H58).
------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
-------------------------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H81).


---------------------------------------------------------------------- apply (@H58).
-----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
------------------------------------------------------------------------intro H81.
apply (@H80 H79).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G F D) as H70.
------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point P (fun X: euclidean__axioms.Point => euclidean__axioms.BetS G X D)) with (y := F).
------------------------------------------------------------- exact H64.
-------------------------------------------------------------apply (@euclidean__tactics.NNPP (P = F) H69).

------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col F E A)) as H71.
------------------------------------------------------------- intro H71.
assert (* Cut *) (euclidean__axioms.Col E F A) as H72.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H72.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (E) (A) H71).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F)))) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))) as H77.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F)) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H73.
-------------------------------------------------------------- apply (@H58).
---------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
----------------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (A) (H11) H72).


------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E A F E A) as H72.
-------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (F) (E) (A)).
---------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (F) (E) (A) H71).

-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E A F E G) as H73.
--------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (E) (A) (F) (E) (A) (F) (G) (H72) (H48) H46).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E G F E A) as H74.
---------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (E) (A) (F) (E) (G) H73).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E G) as H75.
----------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E G)))))))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E G)))))))) as __TmpHyp.
------------------------------------------------------------------- exact H75.
------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E G))))))))) as H76.
-------------------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------------------- destruct H76 as [x H76].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F x) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong x V u v) /\ (euclidean__axioms.nCol F E G))))))))) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [x0 H77].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E F x) /\ ((euclidean__defs.Out E G x0) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x E u) /\ ((euclidean__axioms.Cong E x0 E v) /\ ((euclidean__axioms.Cong x x0 u v) /\ (euclidean__axioms.nCol F E G))))))))) as H78.
---------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------- destruct H78 as [x1 H78].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E F x) /\ ((euclidean__defs.Out E G x0) /\ ((euclidean__defs.Out E F x1) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E v) /\ ((euclidean__axioms.Cong x x0 x1 v) /\ (euclidean__axioms.nCol F E G))))))))) as H79.
----------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------- destruct H79 as [x2 H79].
assert (* AndElim *) ((euclidean__defs.Out E F x) /\ ((euclidean__defs.Out E G x0) /\ ((euclidean__defs.Out E F x1) /\ ((euclidean__defs.Out E A x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G)))))))) as H80.
------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------ destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__defs.Out E G x0) /\ ((euclidean__defs.Out E F x1) /\ ((euclidean__defs.Out E A x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G))))))) as H82.
------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__defs.Out E F x1) /\ ((euclidean__defs.Out E A x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G)))))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__defs.Out E A x2) /\ ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G))))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Cong E x E x1) /\ ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G)))) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Cong E x0 E x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G))) as H90.
----------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol F E G)) as H92.
------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as H94.
------------------------------------------------------------------------------- exact H73.
------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as __TmpHyp0.
-------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A))))))))) as H95.
--------------------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------------------- destruct H95 as [x3 H95].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F x3) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E x3 E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong x3 V u v) /\ (euclidean__axioms.nCol F E A))))))))) as H96.
---------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------- destruct H96 as [x4 H96].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E F x3) /\ ((euclidean__defs.Out E A x4) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E x3 E u) /\ ((euclidean__axioms.Cong E x4 E v) /\ ((euclidean__axioms.Cong x3 x4 u v) /\ (euclidean__axioms.nCol F E A))))))))) as H97.
----------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------- destruct H97 as [x5 H97].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E F x3) /\ ((euclidean__defs.Out E A x4) /\ ((euclidean__defs.Out E F x5) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E v) /\ ((euclidean__axioms.Cong x3 x4 x5 v) /\ (euclidean__axioms.nCol F E A))))))))) as H98.
------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------ destruct H98 as [x6 H98].
assert (* AndElim *) ((euclidean__defs.Out E F x3) /\ ((euclidean__defs.Out E A x4) /\ ((euclidean__defs.Out E F x5) /\ ((euclidean__defs.Out E G x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A)))))))) as H99.
------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__defs.Out E A x4) /\ ((euclidean__defs.Out E F x5) /\ ((euclidean__defs.Out E G x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A))))))) as H101.
-------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__defs.Out E F x5) /\ ((euclidean__defs.Out E G x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A)))))) as H103.
--------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__defs.Out E G x6) /\ ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A))))) as H105.
---------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Cong E x3 E x5) /\ ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A)))) as H107.
----------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Cong E x4 E x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A))) as H109.
------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol F E A)) as H111.
------------------------------------------------------------------------------------------- exact H110.
------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as H113.
-------------------------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as __TmpHyp1.
--------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A))))))))) as H114.
---------------------------------------------------------------------------------------------- exact __TmpHyp1.
---------------------------------------------------------------------------------------------- destruct H114 as [x7 H114].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F x7) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x7 E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong x7 V u v) /\ (euclidean__axioms.nCol F E A))))))))) as H115.
----------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------- destruct H115 as [x8 H115].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E F x7) /\ ((euclidean__defs.Out E A x8) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x7 E u) /\ ((euclidean__axioms.Cong E x8 E v) /\ ((euclidean__axioms.Cong x7 x8 u v) /\ (euclidean__axioms.nCol F E A))))))))) as H116.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ destruct H116 as [x9 H116].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E F x7) /\ ((euclidean__defs.Out E A x8) /\ ((euclidean__defs.Out E F x9) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E v) /\ ((euclidean__axioms.Cong x7 x8 x9 v) /\ (euclidean__axioms.nCol F E A))))))))) as H117.
------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------- destruct H117 as [x10 H117].
assert (* AndElim *) ((euclidean__defs.Out E F x7) /\ ((euclidean__defs.Out E A x8) /\ ((euclidean__defs.Out E F x9) /\ ((euclidean__defs.Out E A x10) /\ ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A)))))))) as H118.
-------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__defs.Out E A x8) /\ ((euclidean__defs.Out E F x9) /\ ((euclidean__defs.Out E A x10) /\ ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A))))))) as H120.
--------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__defs.Out E F x9) /\ ((euclidean__defs.Out E A x10) /\ ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A)))))) as H122.
---------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__defs.Out E A x10) /\ ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A))))) as H124.
----------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Cong E x7 E x9) /\ ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A)))) as H126.
------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Cong E x8 E x10) /\ ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A))) as H128.
------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Cong x7 x8 x9 x10) /\ (euclidean__axioms.nCol F E A)) as H130.
-------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H132.
--------------------------------------------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H133.
----------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------- destruct H133 as [x11 H133].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x11) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x11 E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong x11 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H134.
------------------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------------------ destruct H134 as [x12 H134].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x11) /\ ((euclidean__defs.Out F D x12) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x11 E u) /\ ((euclidean__axioms.Cong F x12 E v) /\ ((euclidean__axioms.Cong x11 x12 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H135.
------------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------------- destruct H135 as [x13 H135].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x11) /\ ((euclidean__defs.Out F D x12) /\ ((euclidean__defs.Out E G x13) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E v) /\ ((euclidean__axioms.Cong x11 x12 x13 v) /\ (euclidean__axioms.nCol E F D))))))))) as H136.
-------------------------------------------------------------------------------------------------------------- exact H135.
-------------------------------------------------------------------------------------------------------------- destruct H136 as [x14 H136].
assert (* AndElim *) ((euclidean__defs.Out F E x11) /\ ((euclidean__defs.Out F D x12) /\ ((euclidean__defs.Out E G x13) /\ ((euclidean__defs.Out E F x14) /\ ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D)))))))) as H137.
--------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__defs.Out F D x12) /\ ((euclidean__defs.Out E G x13) /\ ((euclidean__defs.Out E F x14) /\ ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D))))))) as H139.
---------------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__defs.Out E G x13) /\ ((euclidean__defs.Out E F x14) /\ ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D)))))) as H141.
----------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__defs.Out E F x14) /\ ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D))))) as H143.
------------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------------ destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong F x11 E x13) /\ ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D)))) as H145.
------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Cong F x12 E x14) /\ ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D))) as H147.
-------------------------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Cong x11 x12 x13 x14) /\ (euclidean__axioms.nCol E F D)) as H149.
--------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H151.
---------------------------------------------------------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H152.
------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------ destruct H152 as [x15 H152].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x15) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x15 E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong x15 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H153.
------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------- destruct H153 as [x16 H153].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x15) /\ ((euclidean__defs.Out F D x16) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x15 E u) /\ ((euclidean__axioms.Cong F x16 E v) /\ ((euclidean__axioms.Cong x15 x16 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H154.
-------------------------------------------------------------------------------------------------------------------------- exact H153.
-------------------------------------------------------------------------------------------------------------------------- destruct H154 as [x17 H154].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x15) /\ ((euclidean__defs.Out F D x16) /\ ((euclidean__defs.Out E A x17) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E v) /\ ((euclidean__axioms.Cong x15 x16 x17 v) /\ (euclidean__axioms.nCol E F D))))))))) as H155.
--------------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------------- destruct H155 as [x18 H155].
assert (* AndElim *) ((euclidean__defs.Out F E x15) /\ ((euclidean__defs.Out F D x16) /\ ((euclidean__defs.Out E A x17) /\ ((euclidean__defs.Out E F x18) /\ ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D)))))))) as H156.
---------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__defs.Out F D x16) /\ ((euclidean__defs.Out E A x17) /\ ((euclidean__defs.Out E F x18) /\ ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D))))))) as H158.
----------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__defs.Out E A x17) /\ ((euclidean__defs.Out E F x18) /\ ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D)))))) as H160.
------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------ destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__defs.Out E F x18) /\ ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D))))) as H162.
------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Cong F x15 E x17) /\ ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D)))) as H164.
-------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Cong F x16 E x18) /\ ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D))) as H166.
--------------------------------------------------------------------------------------------------------------------------------- exact H165.
--------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.Cong x15 x16 x17 x18) /\ (euclidean__axioms.nCol E F D)) as H168.
---------------------------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as H170.
----------------------------------------------------------------------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------ exact H170.
------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F))))))))) as H171.
------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [x19 H171].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E B x19) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x19 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x19 V u v) /\ (euclidean__axioms.nCol B E F))))))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------- exact H171.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [x20 H172].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E B x19) /\ ((euclidean__defs.Out E F x20) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x19 F u) /\ ((euclidean__axioms.Cong E x20 F v) /\ ((euclidean__axioms.Cong x19 x20 u v) /\ (euclidean__axioms.nCol B E F))))))))) as H173.
--------------------------------------------------------------------------------------------------------------------------------------- exact H172.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [x21 H173].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E B x19) /\ ((euclidean__defs.Out E F x20) /\ ((euclidean__defs.Out F C x21) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F v) /\ ((euclidean__axioms.Cong x19 x20 x21 v) /\ (euclidean__axioms.nCol B E F))))))))) as H174.
---------------------------------------------------------------------------------------------------------------------------------------- exact H173.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [x22 H174].
assert (* AndElim *) ((euclidean__defs.Out E B x19) /\ ((euclidean__defs.Out E F x20) /\ ((euclidean__defs.Out F C x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F)))))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__defs.Out E F x20) /\ ((euclidean__defs.Out F C x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F))))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__defs.Out F C x21) /\ ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F)))))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__defs.Out F E x22) /\ ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F))))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.Cong E x19 F x21) /\ ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F)))) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.Cong E x20 F x22) /\ ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F))) as H185.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.Cong x19 x20 x21 x22) /\ (euclidean__axioms.nCol B E F)) as H187.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as H189.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B))))))))) as H190.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [x23 H190].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E F x23) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x23 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x23 V u v) /\ (euclidean__axioms.nCol F E B))))))))) as H191.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [x24 H191].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E F x23) /\ ((euclidean__defs.Out E B x24) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x23 F u) /\ ((euclidean__axioms.Cong E x24 F v) /\ ((euclidean__axioms.Cong x23 x24 u v) /\ (euclidean__axioms.nCol F E B))))))))) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [x25 H192].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E F x23) /\ ((euclidean__defs.Out E B x24) /\ ((euclidean__defs.Out F E x25) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F v) /\ ((euclidean__axioms.Cong x23 x24 x25 v) /\ (euclidean__axioms.nCol F E B))))))))) as H193.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [x26 H193].
assert (* AndElim *) ((euclidean__defs.Out E F x23) /\ ((euclidean__defs.Out E B x24) /\ ((euclidean__defs.Out F E x25) /\ ((euclidean__defs.Out F C x26) /\ ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B)))))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__defs.Out E B x24) /\ ((euclidean__defs.Out F E x25) /\ ((euclidean__defs.Out F C x26) /\ ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B))))))) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__defs.Out F E x25) /\ ((euclidean__defs.Out F C x26) /\ ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B)))))) as H198.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__defs.Out F C x26) /\ ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B))))) as H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.Cong E x23 F x25) /\ ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B)))) as H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.Cong E x24 F x26) /\ ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B))) as H204.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.Cong x23 x24 x25 x26) /\ (euclidean__axioms.nCol F E B)) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H205.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H206 as [H206 H207].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H42.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp6.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H209.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [x27 H209].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x27 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x27 V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H210.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [x28 H210].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x27 F u) /\ ((euclidean__axioms.Cong E x28 F v) /\ ((euclidean__axioms.Cong x27 x28 u v) /\ (euclidean__axioms.nCol A E F))))))))) as H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [x29 H211].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F D x29) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F v) /\ ((euclidean__axioms.Cong x27 x28 x29 v) /\ (euclidean__axioms.nCol A E F))))))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H212 as [x30 H212].
assert (* AndElim *) ((euclidean__defs.Out E A x27) /\ ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F D x29) /\ ((euclidean__defs.Out F E x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__defs.Out E F x28) /\ ((euclidean__defs.Out F D x29) /\ ((euclidean__defs.Out F E x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))))))) as H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__defs.Out F D x29) /\ ((euclidean__defs.Out F E x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))))) as H217.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__defs.Out F E x30) /\ ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))))) as H219.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Cong E x27 F x29) /\ ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)))) as H221.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.Cong E x28 F x30) /\ ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.Cong x27 x28 x29 x30) /\ (euclidean__axioms.nCol A E F)) as H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H227.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp7.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H228.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp7.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [x31 H228].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x31) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x31 F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong x31 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [x32 H229].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x31) /\ ((euclidean__defs.Out F D x32) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x31 F u) /\ ((euclidean__axioms.Cong F x32 F v) /\ ((euclidean__axioms.Cong x31 x32 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H229.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H230 as [x33 H230].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x31) /\ ((euclidean__defs.Out F D x32) /\ ((euclidean__defs.Out F D x33) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F v) /\ ((euclidean__axioms.Cong x31 x32 x33 v) /\ (euclidean__axioms.nCol E F D))))))))) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [x34 H231].
assert (* AndElim *) ((euclidean__defs.Out F E x31) /\ ((euclidean__defs.Out F D x32) /\ ((euclidean__defs.Out F D x33) /\ ((euclidean__defs.Out F E x34) /\ ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D)))))))) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__defs.Out F D x32) /\ ((euclidean__defs.Out F D x33) /\ ((euclidean__defs.Out F E x34) /\ ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D))))))) as H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
assert (* AndElim *) ((euclidean__defs.Out F D x33) /\ ((euclidean__defs.Out F E x34) /\ ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D)))))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((euclidean__defs.Out F E x34) /\ ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D))))) as H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((euclidean__axioms.Cong F x31 F x33) /\ ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D)))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [H240 H241].
assert (* AndElim *) ((euclidean__axioms.Cong F x32 F x34) /\ ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((euclidean__axioms.Cong x31 x32 x33 x34) /\ (euclidean__axioms.nCol E F D)) as H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp8.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp8.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [x35 H247].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out F E x35) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x35 E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong x35 V u v) /\ (euclidean__axioms.nCol E F D))))))))) as H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H247.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H248 as [x36 H248].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out F E x35) /\ ((euclidean__defs.Out F D x36) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x35 E u) /\ ((euclidean__axioms.Cong F x36 E v) /\ ((euclidean__axioms.Cong x35 x36 u v) /\ (euclidean__axioms.nCol E F D))))))))) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H249 as [x37 H249].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out F E x35) /\ ((euclidean__defs.Out F D x36) /\ ((euclidean__defs.Out E A x37) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E v) /\ ((euclidean__axioms.Cong x35 x36 x37 v) /\ (euclidean__axioms.nCol E F D))))))))) as H250.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [x38 H250].
assert (* AndElim *) ((euclidean__defs.Out F E x35) /\ ((euclidean__defs.Out F D x36) /\ ((euclidean__defs.Out E A x37) /\ ((euclidean__defs.Out E F x38) /\ ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D)))))))) as H251.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((euclidean__defs.Out F D x36) /\ ((euclidean__defs.Out E A x37) /\ ((euclidean__defs.Out E F x38) /\ ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D))))))) as H253.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((euclidean__defs.Out E A x37) /\ ((euclidean__defs.Out E F x38) /\ ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D)))))) as H255.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [H255 H256].
assert (* AndElim *) ((euclidean__defs.Out E F x38) /\ ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D))))) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H257 as [H257 H258].
assert (* AndElim *) ((euclidean__axioms.Cong F x35 E x37) /\ ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D)))) as H259.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((euclidean__axioms.Cong F x36 E x38) /\ ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D))) as H261.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H261 as [H261 H262].
assert (* AndElim *) ((euclidean__axioms.Cong x35 x36 x37 x38) /\ (euclidean__axioms.nCol E F D)) as H263.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [H263 H264].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H265.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp9.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp9.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H266 as [x39 H266].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out E A x39) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x39 F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong x39 V u v) /\ (euclidean__axioms.nCol A E F))))))))) as H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H267 as [x40 H267].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out E A x39) /\ ((euclidean__defs.Out E F x40) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x39 F u) /\ ((euclidean__axioms.Cong E x40 F v) /\ ((euclidean__axioms.Cong x39 x40 u v) /\ (euclidean__axioms.nCol A E F))))))))) as H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [x41 H268].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out E A x39) /\ ((euclidean__defs.Out E F x40) /\ ((euclidean__defs.Out F E x41) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F v) /\ ((euclidean__axioms.Cong x39 x40 x41 v) /\ (euclidean__axioms.nCol A E F))))))))) as H269.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [x42 H269].
assert (* AndElim *) ((euclidean__defs.Out E A x39) /\ ((euclidean__defs.Out E F x40) /\ ((euclidean__defs.Out F E x41) /\ ((euclidean__defs.Out F D x42) /\ ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F)))))))) as H270.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H269.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((euclidean__defs.Out E F x40) /\ ((euclidean__defs.Out F E x41) /\ ((euclidean__defs.Out F D x42) /\ ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F))))))) as H272.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((euclidean__defs.Out F E x41) /\ ((euclidean__defs.Out F D x42) /\ ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F)))))) as H274.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H273.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H274 as [H274 H275].
assert (* AndElim *) ((euclidean__defs.Out F D x42) /\ ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F))))) as H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H275.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H276 as [H276 H277].
assert (* AndElim *) ((euclidean__axioms.Cong E x39 F x41) /\ ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F)))) as H278.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H277.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((euclidean__axioms.Cong E x40 F x42) /\ ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F))) as H280.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H279.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((euclidean__axioms.Cong x39 x40 x41 x42) /\ (euclidean__axioms.nCol A E F)) as H282.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [H282 H283].
exact H93.
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E G F)) as H76.
------------------------------------------------------------------ intro H76.
assert (* Cut *) (euclidean__axioms.Col F E G) as H77.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H77.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (G) (F) H76).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H78.
--------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E)))) as H80.
---------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))) as H82.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E)) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
exact H82.
------------------------------------------------------------------- apply (@H58).
--------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
---------------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (F) (E) (G) (H75) H77).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Triangle E G F) as H77.
------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (G) (F) H76).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA G E F E F D) as H78.
-------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H78.
--------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
---------------------------------------------------------------------- apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
---------------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
--------------------------------------------------------------------- apply (@H78 (E) (G) (F) (D) (H77) H70).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D E F D) as H79.
--------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (G) (E) (F) (E) (F) (D) (E) (F) (D) (H78) H51).
--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA E F D E F D)) as H80.
---------------------------------------------------------------------- apply (@lemma__angletrichotomy.lemma__angletrichotomy (E) (F) (D) (E) (F) (D) H79).
---------------------------------------------------------------------- apply (@H58).
-----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (G)).
------------------------------------------------------------------------intro H81.
apply (@H80 H79).


-------------------------------------- assert (* Cut *) ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as H47.
--------------------------------------- exact H33.
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H48.
---------------------------------------- assert (* Cut *) ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as H48.
----------------------------------------- exact H47.
----------------------------------------- assert (* Cut *) ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as __TmpHyp.
------------------------------------------ exact H48.
------------------------------------------ assert (A = E \/ (A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E))))) as H49.
------------------------------------------- exact __TmpHyp.
------------------------------------------- destruct H49 as [H49|H49].
-------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H50.
--------------------------------------------- intro H50.
apply (@H13 H49).
--------------------------------------------- exact H50.
-------------------------------------------- assert (A = G \/ (E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50|H50].
---------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq H6 F)) as H51.
----------------------------------------------- intro H51.
assert (* Cut *) (euclidean__axioms.Col C D F) as H52.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H52.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H14).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H53.
-------------------------------------------------- exact H52.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H55.
--------------------------------------------------- exact H54.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H57.
---------------------------------------------------- exact H56.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H59.
----------------------------------------------------- exact H58.
----------------------------------------------------- destruct H59 as [H59 H60].
exact H59.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D G F) as H53.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (G) (F)).
--------------------------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False (D) (G) (F) (H53)).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (G) (F) (H28) (H52) H25).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A F) as H54.
-------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 E B) -> ((euclidean__defs.CongA A0 E F E F D) -> ((euclidean__axioms.TS A0 E F D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.BetS A0 H6 D) -> ((euclidean__axioms.nCol E F A0) -> ((euclidean__axioms.Col A0 E B) -> ((euclidean__axioms.neq A0 E) -> ((euclidean__defs.CongA E F D A0 E F) -> ((euclidean__defs.Meet A0 B C D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.Col B A0 G) -> ((euclidean__axioms.Col B A0 E) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 G E) -> ((euclidean__axioms.Col A0 E G) -> ((euclidean__defs.Supp A0 E F F B) -> ((euclidean__defs.CongA A0 E F D F E) -> ((~(euclidean__axioms.BetS A0 E G)) -> ((~(euclidean__defs.Out E A0 G)) -> (euclidean__axioms.Col D A0 F))))))))))))))))))))))) with (x := A).
---------------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
exact H53.

--------------------------------------------------- exact H50.
--------------------------------------------------- exact H.
--------------------------------------------------- exact H1.
--------------------------------------------------- exact H2.
--------------------------------------------------- exact H3.
--------------------------------------------------- exact H8.
--------------------------------------------------- exact H11.
--------------------------------------------------- exact H12.
--------------------------------------------------- exact H13.
--------------------------------------------------- exact H16.
--------------------------------------------------- exact H20.
--------------------------------------------------- exact H23.
--------------------------------------------------- exact H27.
--------------------------------------------------- exact H29.
--------------------------------------------------- exact H30.
--------------------------------------------------- exact H31.
--------------------------------------------------- exact H32.
--------------------------------------------------- exact H33.
--------------------------------------------------- exact H36.
--------------------------------------------------- exact H42.
--------------------------------------------------- exact H45.
--------------------------------------------------- exact H46.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H6 D) as H55.
--------------------------------------------------- right.
right.
right.
right.
left.
exact H8.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A H6) as H56.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H56.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (H6) (D) H55).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H57.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A)))) as H59.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A)) as H63.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- destruct H63 as [H63 H64].
exact H61.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H57.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H57.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (H6) (D) H8).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D)) as H60.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H60 as [H60 H61].
exact H61.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H58.
------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (D) H57).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A F H6) as H59.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (F) (H6)).
--------------------------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False (A) (F) (H6) (H59)).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (A) (F) (H6) (H54) (H56) H58).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F A) as H60.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A H6) /\ ((euclidean__axioms.Col F H6 A) /\ ((euclidean__axioms.Col H6 A F) /\ ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A))))) as H60.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (H6) H59).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F A H6) /\ ((euclidean__axioms.Col F H6 A) /\ ((euclidean__axioms.Col H6 A F) /\ ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A))))) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col F H6 A) /\ ((euclidean__axioms.Col H6 A F) /\ ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A)))) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col H6 A F) /\ ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A)) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F E) as H61.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H61.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (H6) H10).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E)))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E)) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A E) as H62.
---------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (A) (E)).
-----------------------------------------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False (F) (A) (E) (H62)).
------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H6) (F) (A) (E) (H60) (H61) H51).


---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H63.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H63.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (E) H62).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)))) as H66.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))) as H68.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)) as H70.
---------------------------------------------------------------- exact H69.
---------------------------------------------------------------- destruct H70 as [H70 H71].
exact H68.
----------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17)).
------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (D)).
-------------------------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (A) (H11) H63).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A F D) as H52.
------------------------------------------------ apply (@eq__ind euclidean__axioms.Point H6 (fun X: euclidean__axioms.Point => euclidean__axioms.BetS A X D)) with (y := F).
------------------------------------------------- exact H8.
-------------------------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H51).

------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col E A F)) as H53.
------------------------------------------------- intro H53.
assert (* Cut *) (euclidean__axioms.Col E F A) as H54.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H54.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (F) H53).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E)))) as H57.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E)) as H61.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H61 as [H61 H62].
exact H61.
-------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17)).
---------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (F) (D)).
----------------------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (A) (H11) H54).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle E A F) as H54.
-------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (A) (F) H53).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A E F E F D) as H55.
--------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H55.
---------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
----------------------------------------------------- apply (@proposition__16.proposition__16 (A0) (B0) (C0) (D0) (__) __0).
----------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
---------------------------------------------------- apply (@H55 (E) (A) (F) (D) (H54) H52).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E F D A E F) as H56.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 E B) -> ((euclidean__defs.CongA A0 E F E F D) -> ((euclidean__axioms.TS A0 E F D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.BetS A0 H6 D) -> ((euclidean__axioms.nCol E F A0) -> ((euclidean__axioms.Col A0 E B) -> ((euclidean__axioms.neq A0 E) -> ((euclidean__defs.CongA E F D A0 E F) -> ((euclidean__defs.Meet A0 B C D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.Col B A0 G) -> ((euclidean__axioms.Col B A0 E) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 G E) -> ((euclidean__axioms.Col A0 E G) -> ((euclidean__defs.Supp A0 E F F B) -> ((euclidean__defs.CongA A0 E F D F E) -> ((~(euclidean__axioms.BetS A0 E G)) -> ((~(euclidean__defs.Out E A0 G)) -> ((euclidean__axioms.BetS A0 F D) -> ((~(euclidean__axioms.Col E A0 F)) -> ((euclidean__axioms.Triangle E A0 F) -> ((euclidean__defs.LtA A0 E F E F D) -> (euclidean__defs.CongA E F D A0 E F))))))))))))))))))))))))))) with (x := A).
-----------------------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
exact H64.

----------------------------------------------------- exact H50.
----------------------------------------------------- exact H.
----------------------------------------------------- exact H1.
----------------------------------------------------- exact H2.
----------------------------------------------------- exact H3.
----------------------------------------------------- exact H8.
----------------------------------------------------- exact H11.
----------------------------------------------------- exact H12.
----------------------------------------------------- exact H13.
----------------------------------------------------- exact H16.
----------------------------------------------------- exact H20.
----------------------------------------------------- exact H23.
----------------------------------------------------- exact H27.
----------------------------------------------------- exact H29.
----------------------------------------------------- exact H30.
----------------------------------------------------- exact H31.
----------------------------------------------------- exact H32.
----------------------------------------------------- exact H33.
----------------------------------------------------- exact H36.
----------------------------------------------------- exact H42.
----------------------------------------------------- exact H45.
----------------------------------------------------- exact H46.
----------------------------------------------------- exact H52.
----------------------------------------------------- exact H53.
----------------------------------------------------- exact H54.
----------------------------------------------------- exact H55.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D E F D) as H57.
----------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (A) (E) (F) (E) (F) (D) (E) (F) (D) (H55) H56).
----------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H58.
------------------------------------------------------ intro H58.
assert (* Cut *) (~(euclidean__defs.LtA E F D E F D)) as H59.
------------------------------------------------------- apply (@lemma__angletrichotomy.lemma__angletrichotomy (E) (F) (D) (E) (F) (D) H57).
------------------------------------------------------- apply (@H53).
--------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (E) (A) (F)).
---------------------------------------------------------intro H60.
apply (@H59 H57).


------------------------------------------------------ exact H58.
---------------------------------------------- assert (E = G \/ (euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E))) as H51.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H51 as [H51|H51].
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H52.
------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> (euclidean__axioms.Col C D E0))))))))))))))))))))))))))) with (x := E).
--------------------------------------------------intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
exact H28.

-------------------------------------------------- exact H51.
-------------------------------------------------- exact H.
-------------------------------------------------- exact H1.
-------------------------------------------------- exact H2.
-------------------------------------------------- exact H10.
-------------------------------------------------- exact H11.
-------------------------------------------------- exact H12.
-------------------------------------------------- exact H13.
-------------------------------------------------- exact H16.
-------------------------------------------------- exact H17.
-------------------------------------------------- exact H18.
-------------------------------------------------- exact H19.
-------------------------------------------------- exact H30.
-------------------------------------------------- exact H32.
-------------------------------------------------- exact H33.
-------------------------------------------------- exact H35.
-------------------------------------------------- exact H36.
-------------------------------------------------- exact H37.
-------------------------------------------------- exact H38.
-------------------------------------------------- exact H40.
-------------------------------------------------- exact H41.
-------------------------------------------------- exact H42.
-------------------------------------------------- exact H43.
-------------------------------------------------- exact H44.
-------------------------------------------------- exact H45.
-------------------------------------------------- exact H46.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H53.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H53.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (D) H14).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H54.
---------------------------------------------------- exact H53.
---------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)))) as H56.
----------------------------------------------------- exact H55.
----------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))) as H58.
------------------------------------------------------ exact H57.
------------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C)) as H60.
------------------------------------------------------- exact H59.
------------------------------------------------------- destruct H60 as [H60 H61].
exact H60.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H54.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
----------------------------------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H54)).
-----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (E) (F) (H52) (H53) H25).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H55.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H55.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (F) H54).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H56.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D)))) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))) as H60.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D)) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [H62 H63].
exact H58.
---------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq E F)) as H56.
----------------------------------------------------- intro H56.
assert (* Cut *) (euclidean__axioms.Col F D H6) as H57.
------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (F) (D) (H6)).
-------------------------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False (F) (D) (H6) (H57)).
--------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (F) (D) (H6) (H55) (H10) H56).


------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D H6 F) as H58.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F H6) /\ ((euclidean__axioms.Col D H6 F) /\ ((euclidean__axioms.Col H6 F D) /\ ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F))))) as H58.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (D) (H6) H57).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D F H6) /\ ((euclidean__axioms.Col D H6 F) /\ ((euclidean__axioms.Col H6 F D) /\ ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F))))) as H59.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col D H6 F) /\ ((euclidean__axioms.Col H6 F D) /\ ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F)))) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col H6 F D) /\ ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F))) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F)) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
exact H61.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H6 D) as H59.
-------------------------------------------------------- right.
right.
right.
right.
left.
exact H8.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H6 A) as H60.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H60.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (H6) (D) H59).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H61.
----------------------------------------------------------- exact H60.
----------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A)))) as H63.
------------------------------------------------------------ exact H62.
------------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))) as H65.
------------------------------------------------------------- exact H64.
------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A)) as H67.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H6 D) as H61.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H61.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (H6) (D) H8).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H62.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D)) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
exact H62.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D H6) as H62.
----------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H6) (D) H61).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F A) as H63.
------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (H6) (F) (A)).
-------------------------------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False (H6) (F) (A) (H63)).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (H6) (F) (A) (H58) (H60) H62).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H6 F E) as H64.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H64.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (H6) H10).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H65.
--------------------------------------------------------------- exact H64.
--------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E)))) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))) as H69.
----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E)) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
exact H72.
------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq H6 F)) as H65.
-------------------------------------------------------------- intro H65.
assert (* Cut *) (euclidean__axioms.Col F A E) as H66.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (A) (E)).
----------------------------------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False (F) (A) (E) (H66)).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H6) (F) (A) (E) (H63) (H64) H65).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H67.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H67.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (E) H66).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H68.
------------------------------------------------------------------ exact H67.
------------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)))) as H70.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))) as H72.
-------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)) as H74.
--------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------- destruct H74 as [H74 H75].
exact H72.
---------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H55).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H6 D) as H66.
--------------------------------------------------------------- exact H59.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F D) as H67.
---------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point H6 (fun X: euclidean__axioms.Point => euclidean__axioms.Col A X D)) with (y := F).
----------------------------------------------------------------- exact H66.
-----------------------------------------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H65).

---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F A) as H68.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col F D A) /\ ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A))))) as H68.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (D) H67).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col F D A) /\ ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A))))) as H69.
------------------------------------------------------------------- exact H68.
------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col F D A) /\ ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A)))) as H71.
-------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A))) as H73.
--------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A)) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F C) as H69.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H69.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (F) H53).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H70.
-------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)))) as H72.
--------------------------------------------------------------------- exact H71.
--------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))) as H74.
---------------------------------------------------------------------- exact H73.
---------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)) as H76.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- destruct H76 as [H76 H77].
exact H72.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H6 D) as H70.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D C))) as H70.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (F) (C) H39).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D C))) as H71.
--------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D C)) as H73.
---------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H61.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D H6) as H71.
-------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.neq D H6)))))))))))))))))))))))))))))))) with (x := E).
---------------------------------------------------------------------intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
exact H62.

--------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------- exact H.
--------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------- exact H11.
--------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------- exact H13.
--------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------- exact H17.
--------------------------------------------------------------------- exact H18.
--------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------- exact H32.
--------------------------------------------------------------------- exact H33.
--------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------- exact H36.
--------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------- exact H40.
--------------------------------------------------------------------- exact H41.
--------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------- exact H44.
--------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------- exact H46.
--------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------- exact H56.
--------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H72.
--------------------------------------------------------------------- intro H72.
assert (* Cut *) (False) as H73.
---------------------------------------------------------------------- assert (* Cut *) (~(H6 = F)) as H73.
----------------------------------------------------------------------- intro H73.
apply (@H15).
------------------------------------------------------------------------apply (@logic.eq__sym (Point) (D) (F) H72).

----------------------------------------------------------------------- apply (@H65 H73).
---------------------------------------------------------------------- assert (* Cut *) (False) as H74.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- assert False.
------------------------------------------------------------------------exact H74.
------------------------------------------------------------------------ contradiction.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A C) as H73.
---------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (A) (C)).
-----------------------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False (F) (A) (C) (H73)).
------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (F) (A) (C) (H68) (H69) H72).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F A) as H74.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F))))) as H74.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (C) H73).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A F C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F))))) as H75.
------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F)))) as H77.
-------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F))) as H79.
--------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F)) as H81.
---------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H79.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C G) as H75.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H75.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (G) H28).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H76.
-------------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C)))) as H78.
--------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))) as H80.
---------------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C)) as H82.
----------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H76.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D F) as H76.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D))))) as H76.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (G) H75).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D))))) as H77.
--------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D)))) as H79.
---------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D))) as H81.
----------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D)) as H83.
------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
exact H53.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C F) as H77.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H77.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (F) H76).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H78.
---------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)))) as H80.
----------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))) as H82.
------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------ destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C)) as H84.
------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H78.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H78.
--------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H25).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G F) as H79.
---------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (G) (F)).
-----------------------------------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False (C) (G) (F) (H79)).
------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (G) (F) (H75) (H77) H78).


---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F G) as H80.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H80.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (F) H79).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H81.
------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)))) as H83.
-------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))) as H85.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)) as H87.
---------------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H87.
----------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq C F)) as H81.
------------------------------------------------------------------------------ intro H81.
assert (* Cut *) (euclidean__axioms.Col F A G) as H82.
------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (A) (G)).
--------------------------------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False (F) (A) (G) (H82)).
---------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (F) (A) (G) (H74) (H80) H81).


------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A E) as H83.
-------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.Col F A E0)))))))))))))))))))))))))))))))) with (x := E).
---------------------------------------------------------------------------------intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
exact H82.

--------------------------------------------------------------------------------- exact H51.
--------------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------------- exact H10.
--------------------------------------------------------------------------------- exact H11.
--------------------------------------------------------------------------------- exact H12.
--------------------------------------------------------------------------------- exact H13.
--------------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------------- exact H17.
--------------------------------------------------------------------------------- exact H18.
--------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------- exact H30.
--------------------------------------------------------------------------------- exact H32.
--------------------------------------------------------------------------------- exact H33.
--------------------------------------------------------------------------------- exact H35.
--------------------------------------------------------------------------------- exact H36.
--------------------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------------------- exact H40.
--------------------------------------------------------------------------------- exact H41.
--------------------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------------------- exact H44.
--------------------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------------------- exact H46.
--------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------------- exact H56.
--------------------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H84.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H84.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (A) (E) H83).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H85.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F)) as H91.
-------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H89.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H55).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A H6 D) as H82.
------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C D) as H83.
-------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point H6 (fun X: euclidean__axioms.Point => euclidean__axioms.Col A X D)) with (y := C).
--------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------apply (@logic.eq__trans (Point) (H6) (F) (C)).
----------------------------------------------------------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H65).

----------------------------------------------------------------------------------apply (@logic.eq__sym (Point) (C) (F)).
-----------------------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).



-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H84.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H84.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (D) H83).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H85.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)) as H91.
-------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H87.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D A) as H85.
---------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point C (fun X: euclidean__axioms.Point => euclidean__axioms.Col X D A)) with (y := F).
----------------------------------------------------------------------------------- exact H84.
-----------------------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).

---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H86.
----------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.Col C D E0)))))))))))))))))))))))))))))))) with (x := E).
------------------------------------------------------------------------------------intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
exact H111.

------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------ exact H.
------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------ exact H10.
------------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------------ exact H12.
------------------------------------------------------------------------------------ exact H13.
------------------------------------------------------------------------------------ exact H16.
------------------------------------------------------------------------------------ exact H17.
------------------------------------------------------------------------------------ exact H18.
------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------------ exact H33.
------------------------------------------------------------------------------------ exact H35.
------------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------------ exact H38.
------------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------------ exact H41.
------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------ exact H44.
------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------ exact H46.
------------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------------ exact H64.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H87.
------------------------------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point C (fun X: euclidean__axioms.Point => euclidean__axioms.Col X D E)) with (y := F).
------------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).

------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D F E) as H88.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H88.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (D) (E) H87).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H89.
--------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)))) as H91.
---------------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))) as H93.
----------------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F)) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
exact H89.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F A) as H89.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D))))) as H89.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (F) (E) H88).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D))))) as H90.
---------------------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D)))) as H92.
----------------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D))) as H94.
------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D)) as H96.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H68.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H90.
--------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col F D E0) -> ((euclidean__axioms.Col D F E0) -> (euclidean__axioms.neq D F))))))))))))))))))))))))))))))))))) with (x := E).
----------------------------------------------------------------------------------------intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
exact H72.

---------------------------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------------------------- exact H.
---------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------------------------- exact H10.
---------------------------------------------------------------------------------------- exact H11.
---------------------------------------------------------------------------------------- exact H12.
---------------------------------------------------------------------------------------- exact H13.
---------------------------------------------------------------------------------------- exact H16.
---------------------------------------------------------------------------------------- exact H17.
---------------------------------------------------------------------------------------- exact H18.
---------------------------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------------------------- exact H33.
---------------------------------------------------------------------------------------- exact H35.
---------------------------------------------------------------------------------------- exact H36.
---------------------------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------------------------- exact H38.
---------------------------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------------------------- exact H41.
---------------------------------------------------------------------------------------- exact H42.
---------------------------------------------------------------------------------------- exact H43.
---------------------------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------------------------- exact H45.
---------------------------------------------------------------------------------------- exact H46.
---------------------------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------------------------- exact H54.
---------------------------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------------------------- exact H56.
---------------------------------------------------------------------------------------- exact H64.
---------------------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E A) as H91.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (E) (A)).
-----------------------------------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False (F) (E) (A) (H91)).
------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (F) (E) (A) (H88) (H89) H90).


---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H92.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H92.
------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (E) (A) H91).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H93.
------------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F)))) as H95.
-------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))) as H97.
--------------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F)) as H99.
---------------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H93.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (E) (F) (D) (H17) H55).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H57.
------------------------------------------------------ assert (* Cut *) (False) as H57.
------------------------------------------------------- apply (@H56 H18).
------------------------------------------------------- assert False.
--------------------------------------------------------exact H57.
-------------------------------------------------------- contradiction.
------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H58.
------------------------------------------------------- intro H58.
apply (@H56 H18).
------------------------------------------------------- exact H58.
------------------------------------------------ assert (euclidean__axioms.BetS E A G \/ (euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52|H52].
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H53.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E G))) as H53.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (A) (G) H52).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E G))) as H54.
----------------------------------------------------- exact H53.
----------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E G)) as H56.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H56 as [H56 H57].
exact H56.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E A G) as H54.
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (A) (G)).
-----------------------------------------------------right.
right.
exact H52.

----------------------------------------------------- exact H53.
---------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H55.
----------------------------------------------------- intro H55.
apply (@H46 H54).
----------------------------------------------------- exact H55.
-------------------------------------------------- assert (euclidean__axioms.BetS A E G \/ euclidean__axioms.BetS A G E) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53|H53].
---------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H54.
----------------------------------------------------- intro H54.
apply (@H45 H53).
----------------------------------------------------- exact H54.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G A) as H54.
----------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (G) (E) H53).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H55.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E A))) as H55.
------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (A) H54).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E A))) as H56.
-------------------------------------------------------- exact H55.
-------------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E A)) as H58.
--------------------------------------------------------- exact H57.
--------------------------------------------------------- destruct H58 as [H58 H59].
exact H59.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out E A G) as H56.
------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (E) (A) (G)).
--------------------------------------------------------left.
exact H54.

-------------------------------------------------------- exact H55.
------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H57.
-------------------------------------------------------- intro H57.
apply (@H46 H56).
-------------------------------------------------------- exact H57.
---------------------------------------- apply (@H48 H20).
--------------- assert (* Cut *) (A = A) as H21.
---------------- apply (@logic.eq__refl (Point) A).
---------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H22.
----------------- right.
left.
exact H21.
----------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H23.
------------------ right.
right.
right.
right.
right.
exact H.
------------------ assert (* Cut *) (D = D) as H24.
------------------- apply (@logic.eq__refl (Point) D).
------------------- assert (* Cut *) (euclidean__axioms.Col C D D) as H25.
-------------------- right.
right.
left.
exact H24.
-------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H26.
--------------------- right.
right.
right.
right.
right.
exact H0.
--------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H27.
---------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H27.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (H6) (D) H8).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D)) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
exact H13.
---------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H28.
----------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H28.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (H6) (D) H8).
------------------------ assert (* AndElim *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D)) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
exact H15.
----------------------- assert (* Cut *) (euclidean__axioms.BetS E H6 F) as H29.
------------------------ apply (@lemma__collinearbetween.lemma__collinearbetween (A) (B) (C) (D) (E) (F) (H6) (H12) (H14) (H3) (H4) (H27) (H28) (H20) (H8) H10).
------------------------ assert (* Cut *) (euclidean__axioms.BetS F H6 E) as H30.
------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (H6) (F) H29).
------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H31.
-------------------------- exists A.
exists E.
exists F.
exists D.
exists H6.
split.
--------------------------- exact H3.
--------------------------- split.
---------------------------- exact H4.
---------------------------- split.
----------------------------- exact H22.
----------------------------- split.
------------------------------ exact H23.
------------------------------ split.
------------------------------- exact H27.
------------------------------- split.
-------------------------------- exact H26.
-------------------------------- split.
--------------------------------- exact H25.
--------------------------------- split.
---------------------------------- exact H28.
---------------------------------- split.
----------------------------------- exact H20.
----------------------------------- split.
------------------------------------ exact H8.
------------------------------------ exact H30.
-------------------------- exact H31.
Qed.
