Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthantransitive.
Require Export lemma__partnotequalwhole.
Require Export logic.
Definition lemma__midpointunique : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Midpoint A B C) -> ((euclidean__defs.Midpoint A D C) -> (B = D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H1.
- assert (* Cut *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H1.
-- exact H0.
-- assert (* Cut *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as __TmpHyp.
--- exact H1.
--- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H2.
---- exact __TmpHyp.
---- destruct H2 as [H2 H3].
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H4.
----- exact H.
----- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp0.
------ exact H4.
------ assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H5.
------- exact __TmpHyp0.
------- destruct H5 as [H5 H6].
split.
-------- exact H5.
-------- exact H6.
- assert (* Cut *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H2.
-- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H2.
--- exact H1.
--- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp.
---- exact H2.
---- assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H3.
----- exact __TmpHyp.
----- destruct H3 as [H3 H4].
assert (* Cut *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H5.
------ exact H0.
------ assert (* Cut *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as __TmpHyp0.
------- exact H5.
------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H6.
-------- exact __TmpHyp0.
-------- destruct H6 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H8.
--------- exact H.
--------- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp1.
---------- exact H8.
---------- assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
----------- exact __TmpHyp1.
----------- destruct H9 as [H9 H10].
split.
------------ exact H6.
------------ exact H7.
-- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H3.
--- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H5.
----- exact H1.
----- destruct H5 as [H5 H6].
apply (@euclidean__axioms.cn__congruencereflexive (A) B).
--- assert (* Cut *) (~(euclidean__axioms.BetS C D B)) as H4.
---- intro H4.
assert (* Cut *) (euclidean__axioms.BetS B D C) as H5.
----- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H5.
------ exact H2.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H7.
------- exact H1.
------- destruct H7 as [H7 H8].
apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (D) (B) H4).
----- assert (* Cut *) (euclidean__axioms.BetS A B D) as H6.
------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H6.
------- exact H2.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H8.
-------- exact H1.
-------- destruct H8 as [H8 H9].
apply (@euclidean__axioms.axiom__innertransitivity (A) (B) (D) (C) (H8) H5).
------ assert (* Cut *) (euclidean__defs.Lt A B A D) as H7.
------- exists B.
split.
-------- exact H6.
-------- exact H3.
------- assert (* Cut *) (euclidean__axioms.Cong A D C D) as H8.
-------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H8.
--------- exact H2.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H10.
---------- exact H1.
---------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.Cong D A C D) /\ ((euclidean__axioms.Cong D A D C) /\ (euclidean__axioms.Cong A D C D))) as H12.
----------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (D) (D) (C) H9).
----------- assert (* AndElim *) ((euclidean__axioms.Cong D A C D) /\ ((euclidean__axioms.Cong D A D C) /\ (euclidean__axioms.Cong A D C D))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong D A D C) /\ (euclidean__axioms.Cong A D C D)) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
exact H16.
-------- assert (* Cut *) (euclidean__defs.Lt A B C D) as H9.
--------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H9.
---------- exact H2.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H11.
----------- exact H1.
----------- destruct H11 as [H11 H12].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (A) (D) (C) (D) (H7) H8).
--------- assert (* Cut *) (euclidean__axioms.BetS C D B) as H10.
---------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H10.
----------- exact H2.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H12.
------------ exact H1.
------------ destruct H12 as [H12 H13].
exact H4.
---------- assert (* Cut *) (euclidean__axioms.Cong C D C D) as H11.
----------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H11.
------------ exact H2.
------------ destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H13.
------------- exact H1.
------------- destruct H13 as [H13 H14].
apply (@euclidean__axioms.cn__congruencereflexive (C) D).
----------- assert (* Cut *) (euclidean__defs.Lt C D C B) as H12.
------------ exists D.
split.
------------- exact H10.
------------- exact H11.
------------ assert (* Cut *) (euclidean__defs.Lt A B C B) as H13.
------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H13.
-------------- exact H2.
-------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H15.
--------------- exact H1.
--------------- destruct H15 as [H15 H16].
apply (@lemma__lessthantransitive.lemma__lessthantransitive (A) (B) (C) (D) (C) (B) (H9) H12).
------------- assert (* Cut *) (euclidean__axioms.Cong C B B C) as H14.
-------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H14.
--------------- exact H2.
--------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H16.
---------------- exact H1.
---------------- destruct H16 as [H16 H17].
apply (@euclidean__axioms.cn__equalityreverse (C) B).
-------------- assert (* Cut *) (euclidean__defs.Lt A B B C) as H15.
--------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H15.
---------------- exact H2.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H17.
----------------- exact H1.
----------------- destruct H17 as [H17 H18].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (C) (B) (B) (C) (H13) H14).
--------------- assert (* Cut *) (euclidean__axioms.Cong B C A B) as H16.
---------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H16.
----------------- exact H2.
----------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H18.
------------------ exact H1.
------------------ destruct H18 as [H18 H19].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (B) (C) H19).
---------------- assert (* Cut *) (euclidean__defs.Lt A B A B) as H17.
----------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H17.
------------------ exact H2.
------------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
------------------- exact H1.
------------------- destruct H19 as [H19 H20].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (B) (C) (A) (B) (H15) H16).
----------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E A B)) as H18.
------------------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H18.
------------------- exact H2.
------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
-------------------- exact H1.
-------------------- destruct H20 as [H20 H21].
exact H17.
------------------ assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E A B))) as H19.
------------------- exact H18.
------------------- destruct H19 as [E H19].
assert (* AndElim *) ((euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong A E A B)) as H20.
-------------------- exact H19.
-------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H22.
--------------------- exact H2.
--------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
---------------------- exact H1.
---------------------- destruct H24 as [H24 H25].
assert (* Cut *) (~(euclidean__axioms.Cong A E A B)) as H26.
----------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (A) (E) (B) H20).
----------------------- apply (@H26 H21).
---- assert (* Cut *) (~(euclidean__axioms.BetS C B D)) as H5.
----- intro H5.
assert (* Cut *) (euclidean__axioms.BetS D B C) as H6.
------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H6.
------- exact H2.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H8.
-------- exact H1.
-------- destruct H8 as [H8 H9].
apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (B) (D) H5).
------ assert (* Cut *) (euclidean__axioms.BetS A D B) as H7.
------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H7.
-------- exact H2.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
--------- exact H1.
--------- destruct H9 as [H9 H10].
apply (@euclidean__axioms.axiom__innertransitivity (A) (D) (B) (C) (H7) H6).
------- assert (* Cut *) (euclidean__axioms.Cong A D A D) as H8.
-------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H8.
--------- exact H2.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H10.
---------- exact H1.
---------- destruct H10 as [H10 H11].
apply (@euclidean__axioms.cn__congruencereflexive (A) D).
-------- assert (* Cut *) (euclidean__defs.Lt A D A B) as H9.
--------- exists D.
split.
---------- exact H7.
---------- exact H8.
--------- assert (* Cut *) (euclidean__axioms.Cong A B C B) as H10.
---------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H10.
----------- exact H2.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H12.
------------ exact H1.
------------ destruct H12 as [H12 H13].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H14.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (B) (C) H13).
------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
exact H18.
---------- assert (* Cut *) (euclidean__defs.Lt A D C B) as H11.
----------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H11.
------------ exact H2.
------------ destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H13.
------------- exact H1.
------------- destruct H13 as [H13 H14].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (D) (A) (B) (C) (B) (H9) H10).
----------- assert (* Cut *) (euclidean__axioms.BetS C B D) as H12.
------------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H12.
------------- exact H2.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H14.
-------------- exact H1.
-------------- destruct H14 as [H14 H15].
exact H5.
------------ assert (* Cut *) (euclidean__axioms.Cong C B C B) as H13.
------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H13.
-------------- exact H2.
-------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H15.
--------------- exact H1.
--------------- destruct H15 as [H15 H16].
apply (@euclidean__axioms.cn__congruencereflexive (C) B).
------------- assert (* Cut *) (euclidean__defs.Lt C B C D) as H14.
-------------- exists B.
split.
--------------- exact H12.
--------------- exact H13.
-------------- assert (* Cut *) (euclidean__defs.Lt A D C D) as H15.
--------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H15.
---------------- exact H2.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H17.
----------------- exact H1.
----------------- destruct H17 as [H17 H18].
apply (@lemma__lessthantransitive.lemma__lessthantransitive (A) (D) (C) (B) (C) (D) (H11) H14).
--------------- assert (* Cut *) (euclidean__axioms.Cong C D D C) as H16.
---------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H16.
----------------- exact H2.
----------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H18.
------------------ exact H1.
------------------ destruct H18 as [H18 H19].
apply (@euclidean__axioms.cn__equalityreverse (C) D).
---------------- assert (* Cut *) (euclidean__defs.Lt A D D C) as H17.
----------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H17.
------------------ exact H2.
------------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
------------------- exact H1.
------------------- destruct H19 as [H19 H20].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (D) (C) (D) (D) (C) (H15) H16).
----------------- assert (* Cut *) (euclidean__axioms.Cong D C C D) as H18.
------------------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H18.
------------------- exact H2.
------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
-------------------- exact H1.
-------------------- destruct H20 as [H20 H21].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (C) (D) (C) H16).
------------------ assert (* Cut *) (euclidean__defs.Lt A D C D) as H19.
------------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H19.
-------------------- exact H2.
-------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
--------------------- exact H1.
--------------------- destruct H21 as [H21 H22].
exact H15.
------------------- assert (* Cut *) (euclidean__axioms.Cong D C A D) as H20.
-------------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H20.
--------------------- exact H2.
--------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H22.
---------------------- exact H1.
---------------------- destruct H22 as [H22 H23].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (D) (C) H21).
-------------------- assert (* Cut *) (euclidean__axioms.Cong C D A D) as H21.
--------------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H21.
---------------------- exact H2.
---------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H23.
----------------------- exact H1.
----------------------- destruct H23 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Cong C D D A) /\ ((euclidean__axioms.Cong C D A D) /\ (euclidean__axioms.Cong D C D A))) as H25.
------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (D) (C) (A) (D) H20).
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C D D A) /\ ((euclidean__axioms.Cong C D A D) /\ (euclidean__axioms.Cong D C D A))) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong C D A D) /\ (euclidean__axioms.Cong D C D A)) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
exact H28.
--------------------- assert (* Cut *) (euclidean__defs.Lt A D A D) as H22.
---------------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H22.
----------------------- exact H2.
----------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
------------------------ exact H1.
------------------------ destruct H24 as [H24 H25].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (D) (C) (D) (A) (D) (H19) H21).
---------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F A D)) as H23.
----------------------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H23.
------------------------ exact H2.
------------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H25.
------------------------- exact H1.
------------------------- destruct H25 as [H25 H26].
exact H22.
----------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F A D))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [F H24].
assert (* AndElim *) ((euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F A D)) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H27.
-------------------------- exact H2.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H29.
--------------------------- exact H1.
--------------------------- destruct H29 as [H29 H30].
assert (* Cut *) (~(euclidean__axioms.Cong A F A D)) as H31.
---------------------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (A) (F) (D) H25).
---------------------------- apply (@H31 H26).
----- assert (* Cut *) (euclidean__axioms.BetS C D A) as H6.
------ assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H6.
------- exact H2.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H8.
-------- exact H1.
-------- destruct H8 as [H8 H9].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (C) H6).
------ assert (* Cut *) (euclidean__axioms.BetS C B A) as H7.
------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H7.
-------- exact H2.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
--------- exact H1.
--------- destruct H9 as [H9 H10].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (C) H9).
------- assert (* Cut *) (B = D) as H8.
-------- assert (* AndElim *) ((euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D D C)) as H8.
--------- exact H2.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H10.
---------- exact H1.
---------- destruct H10 as [H10 H11].
apply (@euclidean__axioms.axiom__connectivity (C) (B) (D) (A) (H7) (H6) (H5) H4).
-------- exact H8.
Qed.
