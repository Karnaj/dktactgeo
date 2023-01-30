Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__ray3.
Require Export logic.
Definition lemma__equalangleshelper : forall A B C a b c p q, (euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.Out b a p) -> ((euclidean__defs.Out b c q) -> (euclidean__defs.CongA A B C p b q))).
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
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H2 by exact H.
destruct H2 as [U H3].
destruct H3 as [V H4].
destruct H4 as [u H5].
destruct H5 as [v H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
assert (* Cut *) (euclidean__defs.Out b p u) as H21.
- apply (@lemma__ray3.lemma__ray3 b a p u H0 H11).
- assert (* Cut *) (euclidean__defs.Out b q v) as H22.
-- apply (@lemma__ray3.lemma__ray3 b c q v H1 H13).
-- assert (* Cut *) (euclidean__defs.CongA A B C p b q) as H23.
--- exists U.
exists V.
exists u.
exists v.
split.
---- exact H7.
---- split.
----- exact H9.
----- split.
------ exact H21.
------ split.
------- exact H22.
------- split.
-------- exact H15.
-------- split.
--------- exact H17.
--------- split.
---------- exact H19.
---------- exact H20.
--- exact H23.
Qed.
