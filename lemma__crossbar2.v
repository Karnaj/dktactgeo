Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__angledistinct.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__crossbar.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__sameside2.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__04.
Require Export proposition__07.
Definition lemma__crossbar2 : forall (A: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (P: euclidean__axioms.Point) (S: euclidean__axioms.Point) (T: euclidean__axioms.Point), (euclidean__defs.LtA H G A H G P) -> ((euclidean__defs.OS A P G H) -> ((euclidean__defs.Out G H S) -> ((euclidean__defs.Out G P T) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS T X S) /\ (euclidean__defs.Out G A X))))).
Proof.
intro A.
intro G.
intro H.
intro P.
intro S.
intro T.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__axioms.nCol G H P) as H4.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS P V X) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P)))))) as H4.
-- exact H1.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS P V X) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P)))))) as __TmpHyp.
--- exact H4.
--- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS P V X) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P))))))) as H5.
---- exact __TmpHyp.
---- destruct H5 as [x H5].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS A U x) /\ ((euclidean__axioms.BetS P V x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P))))))) as H6.
----- exact H5.
----- destruct H6 as [x0 H6].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS A x0 x) /\ ((euclidean__axioms.BetS P V x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P))))))) as H7.
------ exact H6.
------ destruct H7 as [x1 H7].
assert (* AndElim *) ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS A x0 x) /\ ((euclidean__axioms.BetS P x1 x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P)))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS A x0 x) /\ ((euclidean__axioms.BetS P x1 x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS A x0 x) /\ ((euclidean__axioms.BetS P x1 x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P)))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS P x1 x) /\ ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol G H A) /\ (euclidean__axioms.nCol G H P)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
exact H17.
- assert (* Cut *) (exists (J: euclidean__axioms.Point) (K: euclidean__axioms.Point) (L: euclidean__axioms.Point), (euclidean__axioms.BetS L K J) /\ ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K)))) as H5.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out G H U) /\ ((euclidean__defs.Out G P V) /\ (euclidean__defs.CongA H G A H G X)))) as H5.
--- exact H0.
--- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out G H U) /\ ((euclidean__defs.Out G P V) /\ (euclidean__defs.CongA H G A H G X)))) as __TmpHyp.
---- exact H5.
---- assert (exists U: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out G H U) /\ ((euclidean__defs.Out G P V) /\ (euclidean__defs.CongA H G A H G X))))) as H6.
----- exact __TmpHyp.
----- destruct H6 as [x H6].
assert (exists X: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.BetS x X V) /\ ((euclidean__defs.Out G H x) /\ ((euclidean__defs.Out G P V) /\ (euclidean__defs.CongA H G A H G X))))) as H7.
------ exact H6.
------ destruct H7 as [x0 H7].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.BetS x x0 V) /\ ((euclidean__defs.Out G H x) /\ ((euclidean__defs.Out G P V) /\ (euclidean__defs.CongA H G A H G x0))))) as H8.
------- exact H7.
------- destruct H8 as [x1 H8].
assert (* AndElim *) ((euclidean__axioms.BetS x x0 x1) /\ ((euclidean__defs.Out G H x) /\ ((euclidean__defs.Out G P x1) /\ (euclidean__defs.CongA H G A H G x0)))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out G H x) /\ ((euclidean__defs.Out G P x1) /\ (euclidean__defs.CongA H G A H G x0))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Out G P x1) /\ (euclidean__defs.CongA H G A H G x0)) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
exists x1.
exists x0.
exists x.
split.
----------- exact H9.
----------- split.
------------ exact H11.
------------ split.
------------- exact H13.
------------- exact H14.
-- assert (exists J: euclidean__axioms.Point, (exists (K: euclidean__axioms.Point) (L: euclidean__axioms.Point), (euclidean__axioms.BetS L K J) /\ ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K))))) as H6.
--- exact H5.
--- destruct H6 as [J H6].
assert (exists K: euclidean__axioms.Point, (exists (L: euclidean__axioms.Point), (euclidean__axioms.BetS L K J) /\ ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K))))) as H7.
---- exact H6.
---- destruct H7 as [K H7].
assert (exists L: euclidean__axioms.Point, ((euclidean__axioms.BetS L K J) /\ ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K))))) as H8.
----- exact H7.
----- destruct H8 as [L H8].
assert (* AndElim *) ((euclidean__axioms.BetS L K J) /\ ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out G H L) /\ ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Out G P J) /\ (euclidean__defs.CongA H G A H G K)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.nCol H G K) as H15.
--------- apply (@euclidean__tactics.nCol__notCol (H) (G) (K)).
----------apply (@euclidean__tactics.nCol__not__Col (H) (G) (K)).
-----------apply (@lemma__equalanglesNC.lemma__equalanglesNC (H) (G) (A) (H) (G) (K) H14).


--------- assert (* Cut *) (~(euclidean__axioms.Col L G J)) as H16.
---------- intro H16.
assert (* Cut *) (euclidean__axioms.Col G H L) as H17.
----------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (H) (L) H11).
----------- assert (* Cut *) (euclidean__axioms.Col G P J) as H18.
------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (P) (J) H13).
------------ assert (* Cut *) (euclidean__axioms.Col L G H) as H19.
------------- assert (* Cut *) ((euclidean__axioms.Col H G L) /\ ((euclidean__axioms.Col H L G) /\ ((euclidean__axioms.Col L G H) /\ ((euclidean__axioms.Col G L H) /\ (euclidean__axioms.Col L H G))))) as H19.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (L) H17).
-------------- assert (* AndElim *) ((euclidean__axioms.Col H G L) /\ ((euclidean__axioms.Col H L G) /\ ((euclidean__axioms.Col L G H) /\ ((euclidean__axioms.Col G L H) /\ (euclidean__axioms.Col L H G))))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col H L G) /\ ((euclidean__axioms.Col L G H) /\ ((euclidean__axioms.Col G L H) /\ (euclidean__axioms.Col L H G)))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col L G H) /\ ((euclidean__axioms.Col G L H) /\ (euclidean__axioms.Col L H G))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col G L H) /\ (euclidean__axioms.Col L H G)) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
exact H24.
------------- assert (* Cut *) (euclidean__axioms.neq G L) as H20.
-------------- apply (@lemma__raystrict.lemma__raystrict (G) (H) (L) H11).
-------------- assert (* Cut *) (euclidean__axioms.neq L G) as H21.
--------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (L) H20).
--------------- assert (* Cut *) (euclidean__axioms.Col G J H) as H22.
---------------- apply (@euclidean__tactics.not__nCol__Col (G) (J) (H)).
-----------------intro H22.
apply (@euclidean__tactics.Col__nCol__False (G) (J) (H) (H22)).
------------------apply (@lemma__collinear4.lemma__collinear4 (L) (G) (J) (H) (H16) (H19) H21).


---------------- assert (* Cut *) (euclidean__axioms.Col J G H) as H23.
----------------- assert (* Cut *) ((euclidean__axioms.Col J G H) /\ ((euclidean__axioms.Col J H G) /\ ((euclidean__axioms.Col H G J) /\ ((euclidean__axioms.Col G H J) /\ (euclidean__axioms.Col H J G))))) as H23.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (J) (H) H22).
------------------ assert (* AndElim *) ((euclidean__axioms.Col J G H) /\ ((euclidean__axioms.Col J H G) /\ ((euclidean__axioms.Col H G J) /\ ((euclidean__axioms.Col G H J) /\ (euclidean__axioms.Col H J G))))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col J H G) /\ ((euclidean__axioms.Col H G J) /\ ((euclidean__axioms.Col G H J) /\ (euclidean__axioms.Col H J G)))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col H G J) /\ ((euclidean__axioms.Col G H J) /\ (euclidean__axioms.Col H J G))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col G H J) /\ (euclidean__axioms.Col H J G)) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
exact H24.
----------------- assert (* Cut *) (euclidean__axioms.Col J G P) as H24.
------------------ assert (* Cut *) ((euclidean__axioms.Col P G J) /\ ((euclidean__axioms.Col P J G) /\ ((euclidean__axioms.Col J G P) /\ ((euclidean__axioms.Col G J P) /\ (euclidean__axioms.Col J P G))))) as H24.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (P) (J) H18).
------------------- assert (* AndElim *) ((euclidean__axioms.Col P G J) /\ ((euclidean__axioms.Col P J G) /\ ((euclidean__axioms.Col J G P) /\ ((euclidean__axioms.Col G J P) /\ (euclidean__axioms.Col J P G))))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col P J G) /\ ((euclidean__axioms.Col J G P) /\ ((euclidean__axioms.Col G J P) /\ (euclidean__axioms.Col J P G)))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col J G P) /\ ((euclidean__axioms.Col G J P) /\ (euclidean__axioms.Col J P G))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col G J P) /\ (euclidean__axioms.Col J P G)) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
exact H29.
------------------ assert (* Cut *) (euclidean__axioms.neq G J) as H25.
------------------- apply (@lemma__raystrict.lemma__raystrict (G) (P) (J) H13).
------------------- assert (* Cut *) (euclidean__axioms.neq J G) as H26.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (J) H25).
-------------------- assert (* Cut *) (euclidean__axioms.Col G H P) as H27.
--------------------- apply (@euclidean__tactics.not__nCol__Col (G) (H) (P)).
----------------------intro H27.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (P) (H27)).
-----------------------apply (@lemma__collinear4.lemma__collinear4 (J) (G) (H) (P) (H23) (H24) H26).


--------------------- apply (@euclidean__tactics.Col__nCol__False (H) (G) (K) (H15)).
----------------------apply (@euclidean__tactics.not__nCol__Col (H) (G) (K)).
-----------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (P) (H4) H27).


---------- assert (* Cut *) (euclidean__axioms.Triangle L G J) as H17.
----------- apply (@euclidean__tactics.nCol__notCol (L) (G) (J) H16).
----------- assert (* Cut *) (euclidean__defs.Out G J T) as H18.
------------ apply (@lemma__ray3.lemma__ray3 (G) (P) (J) (T) (H13) H3).
------------ assert (* Cut *) (euclidean__defs.Out G L S) as H19.
------------- apply (@lemma__ray3.lemma__ray3 (G) (H) (L) (S) (H11) H2).
------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__defs.Out G K M) /\ (euclidean__axioms.BetS S M T)) as H20.
-------------- apply (@lemma__crossbar.lemma__crossbar (L) (G) (J) (K) (S) (T) (H17) (H9) (H19) H18).
-------------- assert (exists M: euclidean__axioms.Point, ((euclidean__defs.Out G K M) /\ (euclidean__axioms.BetS S M T))) as H21.
--------------- exact H20.
--------------- destruct H21 as [M H21].
assert (* AndElim *) ((euclidean__defs.Out G K M) /\ (euclidean__axioms.BetS S M T)) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* Cut *) (euclidean__axioms.BetS T M S) as H24.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (S) (M) (T) H23).
----------------- assert (* Cut *) (euclidean__defs.CongA H G K H G A) as H25.
------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (H) (G) (A) (H) (G) (K) H14).
------------------ assert (* Cut *) (euclidean__axioms.neq G A) as H26.
------------------- assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A)))))) as H26.
-------------------- apply (@lemma__angledistinct.lemma__angledistinct (H) (G) (K) (H) (G) (A) H25).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A)))))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A))))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A)))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A))) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq H A)) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
exact H35.
------------------- assert (* Cut *) (euclidean__axioms.neq G M) as H27.
-------------------- apply (@lemma__raystrict.lemma__raystrict (G) (K) (M) H22).
-------------------- assert (* Cut *) (exists (N: euclidean__axioms.Point), (euclidean__defs.Out G A N) /\ (euclidean__axioms.Cong G N G M)) as H28.
--------------------- apply (@lemma__layoff.lemma__layoff (G) (A) (G) (M) (H26) H27).
--------------------- assert (exists N: euclidean__axioms.Point, ((euclidean__defs.Out G A N) /\ (euclidean__axioms.Cong G N G M))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [N H29].
assert (* AndElim *) ((euclidean__defs.Out G A N) /\ (euclidean__axioms.Cong G N G M)) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
assert (* Cut *) (H = H) as H32.
------------------------ apply (@logic.eq__refl (Point) H).
------------------------ assert (* Cut *) (~(G = H)) as H33.
------------------------- intro H33.
assert (* Cut *) (euclidean__axioms.Col G H P) as H34.
-------------------------- left.
exact H33.
-------------------------- apply (@H16).
---------------------------apply (@euclidean__tactics.not__nCol__Col (L) (G) (J)).
----------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (G) (H) (P) (H4) H34).


------------------------- assert (* Cut *) (euclidean__defs.Out G H H) as H34.
-------------------------- apply (@lemma__ray4.lemma__ray4 (G) (H) (H)).
---------------------------right.
left.
exact H32.

--------------------------- exact H33.
-------------------------- assert (* Cut *) (~(euclidean__axioms.Col H G M)) as H35.
--------------------------- intro H35.
assert (* Cut *) (euclidean__axioms.Col G K M) as H36.
---------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (K) (M) H22).
---------------------------- assert (* Cut *) (euclidean__axioms.Col M G K) as H37.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H37.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (K) (M) H36).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G)))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G)) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
exact H42.
----------------------------- assert (* Cut *) (euclidean__axioms.Col M G H) as H38.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col G H M) /\ ((euclidean__axioms.Col G M H) /\ ((euclidean__axioms.Col M H G) /\ ((euclidean__axioms.Col H M G) /\ (euclidean__axioms.Col M G H))))) as H38.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (G) (M) H35).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G H M) /\ ((euclidean__axioms.Col G M H) /\ ((euclidean__axioms.Col M H G) /\ ((euclidean__axioms.Col H M G) /\ (euclidean__axioms.Col M G H))))) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col G M H) /\ ((euclidean__axioms.Col M H G) /\ ((euclidean__axioms.Col H M G) /\ (euclidean__axioms.Col M G H)))) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col M H G) /\ ((euclidean__axioms.Col H M G) /\ (euclidean__axioms.Col M G H))) as H43.
---------------------------------- exact H42.
---------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col H M G) /\ (euclidean__axioms.Col M G H)) as H45.
----------------------------------- exact H44.
----------------------------------- destruct H45 as [H45 H46].
exact H46.
------------------------------ assert (* Cut *) (euclidean__axioms.neq G M) as H39.
------------------------------- exact H27.
------------------------------- assert (* Cut *) (euclidean__axioms.neq M G) as H40.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (M) H39).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col G K H) as H41.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (K) (H)).
----------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (G) (K) (H) (H41)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (G) (K) (H) (H37) (H38) H40).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col H G K) as H42.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G))))) as H42.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (K) (H) H41).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G))))) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G)))) as H45.
------------------------------------- exact H44.
------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G))) as H47.
-------------------------------------- exact H46.
-------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G)) as H49.
--------------------------------------- exact H48.
--------------------------------------- destruct H49 as [H49 H50].
exact H47.
---------------------------------- apply (@H16).
-----------------------------------apply (@euclidean__tactics.not__nCol__Col (L) (G) (J)).
------------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (H) (G) (K) (H15) H42).


--------------------------- assert (* Cut *) (euclidean__defs.CongA H G M H G M) as H36.
---------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (H) (G) (M)).
-----------------------------apply (@euclidean__tactics.nCol__notCol (H) (G) (M) H35).

---------------------------- assert (* Cut *) (euclidean__defs.Out G M K) as H37.
----------------------------- apply (@lemma__ray5.lemma__ray5 (G) (K) (M) H22).
----------------------------- assert (* Cut *) (euclidean__defs.CongA H G M H G K) as H38.
------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (H) (G) (M) (H) (G) (M) (H) (K) (H36) (H34) H37).
------------------------------ assert (* Cut *) (euclidean__defs.CongA H G M H G A) as H39.
------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H) (G) (M) (H) (G) (K) (H) (G) (A) (H38) H25).
------------------------------- assert (* Cut *) (euclidean__axioms.nCol H G A) as H40.
-------------------------------- apply (@euclidean__tactics.nCol__notCol (H) (G) (A)).
---------------------------------apply (@euclidean__tactics.nCol__not__Col (H) (G) (A)).
----------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (H) (G) (M) (H) (G) (A) H39).


-------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G A) as H41.
--------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (H) (G) (A) H40).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA H G A H G N) as H42.
---------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (H) (G) (A) (H) (G) (A) (H) (N) (H41) (H34) H30).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA H G M H G N) as H43.
----------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H) (G) (M) (H) (G) (A) (H) (G) (N) (H39) H42).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA H G N H G M) as H44.
------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (H) (G) (M) (H) (G) (N) H43).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong G H G H) as H45.
------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) H).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H N H M) as H46.
-------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__defs.CongA B A0 C b a c) -> (euclidean__axioms.Cong B C b c)))) as H46.
--------------------------------------- intro A0.
intro B.
intro C.
intro a.
intro b.
intro c.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B C b c) /\ ((euclidean__defs.CongA A0 B C a b c) /\ (euclidean__defs.CongA A0 C B a c b))) as __2.
---------------------------------------- apply (@proposition__04.proposition__04 (A0) (B) (C) (a) (b) (c) (__) (__0) __1).
---------------------------------------- destruct __2 as [__2 __3].
exact __2.
--------------------------------------- apply (@H46 (G) (H) (N) (G) (H) (M) (H45) (H31) H44).
-------------------------------------- assert (* Cut *) (G = G) as H47.
--------------------------------------- apply (@logic.eq__refl (Point) G).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col G G H) as H48.
---------------------------------------- left.
exact H47.
---------------------------------------- assert (* Cut *) (euclidean__defs.OS A T G H) as H49.
----------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (G) (G) (H) (A) (P) (T) (H1) (H48) H3).
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq S M) as H50.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M T) /\ ((euclidean__axioms.neq S M) /\ (euclidean__axioms.neq S T))) as H50.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (S) (M) (T) H23).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M T) /\ ((euclidean__axioms.neq S M) /\ (euclidean__axioms.neq S T))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq S M) /\ (euclidean__axioms.neq S T)) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
exact H53.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out S M T) as H51.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (S) (M) (T)).
--------------------------------------------right.
right.
exact H23.

-------------------------------------------- exact H50.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out S T M) as H52.
-------------------------------------------- apply (@lemma__ray5.lemma__ray5 (S) (M) (T) H51).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H S) as H53.
--------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (G) (H) (S) H2).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G S H) as H54.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col H S G) /\ ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col G S H) /\ (euclidean__axioms.Col S H G))))) as H54.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (S) H53).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H G S) /\ ((euclidean__axioms.Col H S G) /\ ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col G S H) /\ (euclidean__axioms.Col S H G))))) as H55.
------------------------------------------------ exact H54.
------------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col H S G) /\ ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col G S H) /\ (euclidean__axioms.Col S H G)))) as H57.
------------------------------------------------- exact H56.
------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col S G H) /\ ((euclidean__axioms.Col G S H) /\ (euclidean__axioms.Col S H G))) as H59.
-------------------------------------------------- exact H58.
-------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col G S H) /\ (euclidean__axioms.Col S H G)) as H61.
--------------------------------------------------- exact H60.
--------------------------------------------------- destruct H61 as [H61 H62].
exact H61.
---------------------------------------------- assert (* Cut *) (euclidean__defs.OS A M G H) as H55.
----------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (G) (S) (H) (A) (T) (M) (H49) (H54) H52).
----------------------------------------------- assert (* Cut *) (euclidean__defs.OS M A G H) as H56.
------------------------------------------------ assert (* Cut *) ((euclidean__defs.OS M A G H) /\ ((euclidean__defs.OS A M H G) /\ (euclidean__defs.OS M A H G))) as H56.
------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (G) (H) (A) (M) H55).
------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS M A G H) /\ ((euclidean__defs.OS A M H G) /\ (euclidean__defs.OS M A H G))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__defs.OS A M H G) /\ (euclidean__defs.OS M A H G)) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
------------------------------------------------ assert (* Cut *) (euclidean__defs.OS M N G H) as H57.
------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (G) (G) (H) (M) (A) (N) (H56) (H48) H30).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong N H M H) as H58.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong N H M H) /\ ((euclidean__axioms.Cong N H H M) /\ (euclidean__axioms.Cong H N M H))) as H58.
--------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (H) (N) (H) (M) H46).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong N H M H) /\ ((euclidean__axioms.Cong N H H M) /\ (euclidean__axioms.Cong H N M H))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong N H H M) /\ (euclidean__axioms.Cong H N M H)) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
exact H59.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M H N H) as H59.
--------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (N) (H) (H) H58).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong N G M G) as H60.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong N G M G) /\ ((euclidean__axioms.Cong N G G M) /\ (euclidean__axioms.Cong G N M G))) as H60.
----------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (N) (G) (M) H31).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong N G M G) /\ ((euclidean__axioms.Cong N G G M) /\ (euclidean__axioms.Cong G N M G))) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Cong N G G M) /\ (euclidean__axioms.Cong G N M G)) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
exact H61.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M G N G) as H61.
----------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (N) (G) (G) H60).
----------------------------------------------------- assert (* Cut *) (M = N) as H62.
------------------------------------------------------ apply (@proposition__07.proposition__07 (G) (H) (M) (N) (H33) (H61) (H59) H57).
------------------------------------------------------ assert (* Cut *) (N = M) as H63.
------------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (N) (M) H62).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out G A M) as H64.
-------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point M (fun N0: euclidean__axioms.Point => (euclidean__defs.Out G A N0) -> ((euclidean__axioms.Cong G N0 G M) -> ((euclidean__defs.CongA H G A H G N0) -> ((euclidean__defs.CongA H G M H G N0) -> ((euclidean__defs.CongA H G N0 H G M) -> ((euclidean__axioms.Cong H N0 H M) -> ((euclidean__defs.OS M N0 G H) -> ((euclidean__axioms.Cong N0 H M H) -> ((euclidean__axioms.Cong M H N0 H) -> ((euclidean__axioms.Cong N0 G M G) -> ((euclidean__axioms.Cong M G N0 G) -> ((N0 = M) -> (euclidean__defs.Out G A M)))))))))))))) with (y := N).
---------------------------------------------------------intro H64.
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
assert (* Cut *) (M = M) as H76.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- exact H64.

--------------------------------------------------------- exact H62.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- exact H31.
--------------------------------------------------------- exact H42.
--------------------------------------------------------- exact H43.
--------------------------------------------------------- exact H44.
--------------------------------------------------------- exact H46.
--------------------------------------------------------- exact H57.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- exact H63.
-------------------------------------------------------- exists M.
split.
--------------------------------------------------------- exact H24.
--------------------------------------------------------- exact H64.
Qed.
