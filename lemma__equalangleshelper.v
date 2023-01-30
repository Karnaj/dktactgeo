Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__ray3.
Require Export logic.
Definition lemma__equalangleshelper : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.Out b a p) -> ((euclidean__defs.Out b c q) -> (euclidean__defs.CongA A B C p b q))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro p.
intro q.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H2.
- exact H.
- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H3.
-- exact H2.
-- destruct H3 as [U H3].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H4.
--- exact H3.
--- destruct H4 as [V H4].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H5.
---- exact H4.
---- destruct H5 as [u H5].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H6.
----- exact H5.
----- destruct H6 as [v H6].
assert (* AndElim *) ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))) as H17.
----------- exact H16.
----------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
assert (* Cut *) (euclidean__defs.Out b p u) as H21.
------------- apply (@lemma__ray3.lemma__ray3 (b) (a) (p) (u) (H0) H11).
------------- assert (* Cut *) (euclidean__defs.Out b q v) as H22.
-------------- apply (@lemma__ray3.lemma__ray3 (b) (c) (q) (v) (H1) H13).
-------------- assert (* Cut *) (euclidean__defs.CongA A B C p b q) as H23.
--------------- exists U.
exists V.
exists u.
exists v.
split.
---------------- exact H7.
---------------- split.
----------------- exact H9.
----------------- split.
------------------ exact H21.
------------------ split.
------------------- exact H22.
------------------- split.
-------------------- exact H15.
-------------------- split.
--------------------- exact H17.
--------------------- split.
---------------------- exact H19.
---------------------- exact H20.
--------------- exact H23.
Qed.
