Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__NCorder.
Require Export lemma__TCreflexive.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__EFreflexive : forall (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (p: euclidean__axioms.Point), (euclidean__axioms.BetS a p c) -> ((euclidean__axioms.BetS b p d) -> ((euclidean__axioms.nCol a b c) -> (euclidean__axioms.EF a b c d a b c d))).
Proof.
intro a.
intro b.
intro c.
intro d.
intro p.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.nCol a c b) as H2.
- assert (* Cut *) ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))))) as H2.
-- apply (@lemma__NCorder.lemma__NCorder (a) (b) (c) H1).
-- assert (* AndElim *) ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a)))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
exact H9.
- assert (* Cut *) (~(euclidean__axioms.Col a c d)) as H3.
-- intro H3.
assert (* Cut *) (euclidean__axioms.Col b p d) as H4.
--- right.
right.
right.
right.
left.
exact H0.
--- assert (* Cut *) (euclidean__axioms.Col a p c) as H5.
---- right.
right.
right.
right.
left.
exact H.
---- assert (* Cut *) (euclidean__axioms.Col a c p) as H6.
----- assert (* Cut *) ((euclidean__axioms.Col p a c) /\ ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))))) as H6.
------ apply (@lemma__collinearorder.lemma__collinearorder (a) (p) (c) H5).
------ assert (* AndElim *) ((euclidean__axioms.Col p a c) /\ ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a)))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a)) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
exact H13.
----- assert (* Cut *) (euclidean__axioms.neq a c) as H7.
------ assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c))) as H7.
------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (p) (c) H).
------- assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exact H11.
------ assert (* Cut *) (euclidean__axioms.Col c d p) as H8.
------- apply (@euclidean__tactics.not__nCol__Col (c) (d) (p)).
--------intro H8.
apply (@euclidean__tactics.Col__nCol__False (c) (d) (p) (H8)).
---------apply (@lemma__collinear4.lemma__collinear4 (a) (c) (d) (p) (H3) (H6) H7).


------- assert (* Cut *) (euclidean__axioms.Col d p c) as H9.
-------- assert (* Cut *) ((euclidean__axioms.Col d c p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p c d) /\ ((euclidean__axioms.Col c p d) /\ (euclidean__axioms.Col p d c))))) as H9.
--------- apply (@lemma__collinearorder.lemma__collinearorder (c) (d) (p) H8).
--------- assert (* AndElim *) ((euclidean__axioms.Col d c p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p c d) /\ ((euclidean__axioms.Col c p d) /\ (euclidean__axioms.Col p d c))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p c d) /\ ((euclidean__axioms.Col c p d) /\ (euclidean__axioms.Col p d c)))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col p c d) /\ ((euclidean__axioms.Col c p d) /\ (euclidean__axioms.Col p d c))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col c p d) /\ (euclidean__axioms.Col p d c)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
exact H12.
-------- assert (* Cut *) (euclidean__axioms.Col d p b) as H10.
--------- assert (* Cut *) ((euclidean__axioms.Col p b d) /\ ((euclidean__axioms.Col p d b) /\ ((euclidean__axioms.Col d b p) /\ ((euclidean__axioms.Col b d p) /\ (euclidean__axioms.Col d p b))))) as H10.
---------- apply (@lemma__collinearorder.lemma__collinearorder (b) (p) (d) H4).
---------- assert (* AndElim *) ((euclidean__axioms.Col p b d) /\ ((euclidean__axioms.Col p d b) /\ ((euclidean__axioms.Col d b p) /\ ((euclidean__axioms.Col b d p) /\ (euclidean__axioms.Col d p b))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col p d b) /\ ((euclidean__axioms.Col d b p) /\ ((euclidean__axioms.Col b d p) /\ (euclidean__axioms.Col d p b)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col d b p) /\ ((euclidean__axioms.Col b d p) /\ (euclidean__axioms.Col d p b))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col b d p) /\ (euclidean__axioms.Col d p b)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H18.
--------- assert (* Cut *) (euclidean__axioms.neq p d) as H11.
---------- assert (* Cut *) ((euclidean__axioms.neq p d) /\ ((euclidean__axioms.neq b p) /\ (euclidean__axioms.neq b d))) as H11.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal (b) (p) (d) H0).
----------- assert (* AndElim *) ((euclidean__axioms.neq p d) /\ ((euclidean__axioms.neq b p) /\ (euclidean__axioms.neq b d))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq b p) /\ (euclidean__axioms.neq b d)) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
exact H12.
---------- assert (* Cut *) (euclidean__axioms.neq d p) as H12.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (p) (d) H11).
----------- assert (* Cut *) (euclidean__axioms.Col p c b) as H13.
------------ apply (@euclidean__tactics.not__nCol__Col (p) (c) (b)).
-------------intro H13.
apply (@euclidean__tactics.Col__nCol__False (p) (c) (b) (H13)).
--------------apply (@lemma__collinear4.lemma__collinear4 (d) (p) (c) (b) (H9) (H10) H12).


------------ assert (* Cut *) (euclidean__axioms.Col a p c) as H14.
------------- exact H5.
------------- assert (* Cut *) (euclidean__axioms.Col p c a) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.Col p a c) /\ ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))))) as H15.
--------------- apply (@lemma__collinearorder.lemma__collinearorder (a) (p) (c) H14).
--------------- assert (* AndElim *) ((euclidean__axioms.Col p a c) /\ ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col p c a) /\ ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a)))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col c a p) /\ ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col a c p) /\ (euclidean__axioms.Col c p a)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
exact H18.
-------------- assert (* Cut *) (euclidean__axioms.neq p c) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c))) as H16.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (p) (c) H).
---------------- assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq a p) /\ (euclidean__axioms.neq a c)) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
exact H17.
--------------- assert (* Cut *) (euclidean__axioms.Col c b a) as H17.
---------------- apply (@euclidean__tactics.not__nCol__Col (c) (b) (a)).
-----------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (c) (b) (a) (H17)).
------------------apply (@lemma__collinear4.lemma__collinear4 (p) (c) (b) (a) (H13) (H15) H16).


---------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H18.
----------------- assert (* Cut *) ((euclidean__axioms.Col b c a) /\ ((euclidean__axioms.Col b a c) /\ ((euclidean__axioms.Col a c b) /\ ((euclidean__axioms.Col c a b) /\ (euclidean__axioms.Col a b c))))) as H18.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (c) (b) (a) H17).
------------------ assert (* AndElim *) ((euclidean__axioms.Col b c a) /\ ((euclidean__axioms.Col b a c) /\ ((euclidean__axioms.Col a c b) /\ ((euclidean__axioms.Col c a b) /\ (euclidean__axioms.Col a b c))))) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col b a c) /\ ((euclidean__axioms.Col a c b) /\ ((euclidean__axioms.Col c a b) /\ (euclidean__axioms.Col a b c)))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col a c b) /\ ((euclidean__axioms.Col c a b) /\ (euclidean__axioms.Col a b c))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col c a b) /\ (euclidean__axioms.Col a b c)) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
exact H26.
----------------- apply (@euclidean__tactics.Col__nCol__False (a) (c) (b) (H2)).
------------------apply (@euclidean__tactics.not__nCol__Col (a) (c) (b)).
-------------------intro H19.
apply (@euclidean__tactics.Col__nCol__False (a) (b) (c) (H1) H18).


-- assert (* Cut *) (euclidean__axioms.Triangle a c d) as H4.
--- apply (@euclidean__tactics.nCol__notCol (a) (c) (d) H3).
--- assert (* Cut *) (euclidean__axioms.Triangle a c b) as H5.
---- exact H2.
---- assert (* Cut *) (euclidean__axioms.Cong__3 a c d a c d) as H6.
----- apply (@lemma__TCreflexive.lemma__TCreflexive (a) (c) (d) H4).
----- assert (* Cut *) (euclidean__axioms.Cong__3 a c b a c b) as H7.
------ apply (@lemma__TCreflexive.lemma__TCreflexive (a) (c) (b) H5).
------ assert (* Cut *) (euclidean__axioms.ET a c d a c d) as H8.
------- apply (@euclidean__axioms.axiom__congruentequal (a) (c) (d) (a) (c) (d) H6).
------- assert (* Cut *) (euclidean__axioms.ET a c b a c b) as H9.
-------- apply (@euclidean__axioms.axiom__congruentequal (a) (c) (b) (a) (c) (b) H7).
-------- assert (* Cut *) (euclidean__axioms.Col a c p) as H10.
--------- right.
right.
right.
right.
right.
exact H.
--------- assert (* Cut *) (euclidean__axioms.nCol a c b) as H11.
---------- assert (* Cut *) ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol c b a) /\ ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol a b c) /\ (euclidean__axioms.nCol b c a))))) as H11.
----------- apply (@lemma__NCorder.lemma__NCorder (a) (c) (b) H5).
----------- assert (* AndElim *) ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol c b a) /\ ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol a b c) /\ (euclidean__axioms.nCol b c a))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol c b a) /\ ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol a b c) /\ (euclidean__axioms.nCol b c a)))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol a b c) /\ (euclidean__axioms.nCol b c a))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol a b c) /\ (euclidean__axioms.nCol b c a)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H2.
---------- assert (* Cut *) (euclidean__axioms.TS b a c d) as H12.
----------- exists p.
split.
------------ exact H0.
------------ split.
------------- exact H10.
------------- exact H11.
----------- assert (* Cut *) (euclidean__axioms.EF a b c d a b c d) as H13.
------------ apply (@euclidean__axioms.axiom__paste3 (a) (c) (b) (d) (p) (a) (c) (b) (d) (p) (H9) (H8) (H0)).
-------------left.
exact H.

------------- exact H0.
-------------left.
exact H.

------------ exact H13.
Qed.
