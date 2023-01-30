Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__planeseparation.
Require Export logic.
Definition lemma__samesidetransitive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.OS P Q A B) -> ((euclidean__defs.OS Q R A B) -> (euclidean__defs.OS P R A B)).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro R.
intro H.
intro H0.
assert (* Cut *) (exists (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H1.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H1.
-- exact H0.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as __TmpHyp.
--- exact H1.
--- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H2.
---- exact __TmpHyp.
---- destruct H2 as [x H2].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U x) /\ ((euclidean__axioms.BetS R V x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H3.
----- exact H2.
----- destruct H3 as [x0 H3].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q x0 x) /\ ((euclidean__axioms.BetS R V x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H4.
------ exact H3.
------ destruct H4 as [x1 H4].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS Q x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H5.
------- exact H4.
------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS Q x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS Q x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H15.
------------ exact H.
------------ assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as __TmpHyp0.
------------- exact H15.
------------- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q))))))) as H16.
-------------- exact __TmpHyp0.
-------------- destruct H16 as [x2 H16].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U x2) /\ ((euclidean__axioms.BetS Q V x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q))))))) as H17.
--------------- exact H16.
--------------- destruct H17 as [x3 H17].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col A B x3) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P x3 x2) /\ ((euclidean__axioms.BetS Q V x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q))))))) as H18.
---------------- exact H17.
---------------- destruct H18 as [x4 H18].
assert (* AndElim *) ((euclidean__axioms.Col A B x3) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.BetS P x3 x2) /\ ((euclidean__axioms.BetS Q x4 x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.BetS P x3 x2) /\ ((euclidean__axioms.BetS Q x4 x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q))))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS P x3 x2) /\ ((euclidean__axioms.BetS Q x4 x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS Q x4 x2) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
exists x0.
exists x1.
exists x.
split.
---------------------- exact H5.
---------------------- split.
----------------------- exact H7.
----------------------- split.
------------------------ exact H9.
------------------------ split.
------------------------- exact H11.
------------------------- split.
-------------------------- exact H28.
-------------------------- exact H14.
- assert (exists E: euclidean__axioms.Point, (exists (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H2.
-- exact H1.
-- destruct H2 as [E H2].
assert (exists F: euclidean__axioms.Point, (exists (G: euclidean__axioms.Point), (euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H3.
--- exact H2.
--- destruct H3 as [F H3].
assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))))) as H4.
---- exact H3.
---- destruct H4 as [G H4].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.TS Q A B G) as H15.
---------- exists E.
split.
----------- exact H9.
----------- split.
------------ exact H5.
------------ exact H13.
---------- assert (* Cut *) (euclidean__axioms.TS P A B G) as H16.
----------- apply (@lemma__planeseparation.lemma__planeseparation (A) (B) (P) (Q) (G) (H) H15).
----------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS P M G) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.nCol A B P))) as H17.
------------ exact H16.
------------ assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS P M G) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.nCol A B P)))) as H18.
------------- exact H17.
------------- destruct H18 as [M H18].
assert (* AndElim *) ((euclidean__axioms.BetS P M G) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.nCol A B P))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.nCol A B P)) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* Cut *) (euclidean__defs.OS P R A B) as H23.
---------------- exists G.
exists M.
exists F.
split.
----------------- exact H21.
----------------- split.
------------------ exact H7.
------------------ split.
------------------- exact H19.
------------------- split.
-------------------- exact H11.
-------------------- split.
--------------------- exact H22.
--------------------- exact H14.
---------------- exact H23.
Qed.
