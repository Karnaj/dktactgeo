Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__equalanglessymmetric.
Require Export logic.
Definition lemma__angledistinct : forall A B C a b c, (euclidean__defs.CongA A B C a b c) -> ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ (euclidean__axioms.neq a c)))))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H0.
- assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H0 by exact H.
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [x2 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
- assert (* Cut *) (~(A = B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col A B C) as H2.
--- left.
exact H1.
--- apply (@euclidean__tactics.Col__nCol__False A B C H0 H2).
-- assert (* Cut *) (~(B = C)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- right.
right.
left.
exact H2.
---- apply (@euclidean__tactics.Col__nCol__False A B C H0 H3).
--- assert (* Cut *) (~(A = C)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- right.
left.
exact H3.
----- apply (@euclidean__tactics.Col__nCol__False A B C H0 H4).
---- assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H4.
----- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C a b c H).
----- assert (* Cut *) (euclidean__axioms.nCol a b c) as H5.
------ assert (exists U V u v, (euclidean__defs.Out b a U) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b U B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol a b c)))))))) as H5 by exact H4.
assert (exists U V u v, (euclidean__defs.Out b a U) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b U B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol a b c)))))))) as __TmpHyp by exact H5.
destruct __TmpHyp as [x H6].
destruct H6 as [x0 H7].
destruct H7 as [x1 H8].
destruct H8 as [x2 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H24 by exact H.
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp0 by exact H24.
destruct __TmpHyp0 as [x3 H25].
destruct H25 as [x4 H26].
destruct H26 as [x5 H27].
destruct H27 as [x6 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H23.
------ assert (* Cut *) (~(a = b)) as H6.
------- intro H6.
assert (* Cut *) (euclidean__axioms.Col a b c) as H7.
-------- left.
exact H6.
-------- apply (@euclidean__tactics.Col__nCol__False a b c H5 H7).
------- assert (* Cut *) (~(b = c)) as H7.
-------- intro H7.
assert (* Cut *) (euclidean__axioms.Col a b c) as H8.
--------- right.
right.
left.
exact H7.
--------- apply (@euclidean__tactics.Col__nCol__False a b c H5 H8).
-------- assert (* Cut *) (~(a = c)) as H8.
--------- intro H8.
assert (* Cut *) (euclidean__axioms.Col a b c) as H9.
---------- right.
left.
exact H8.
---------- apply (@euclidean__tactics.Col__nCol__False a b c H5 H9).
--------- split.
---------- exact H1.
---------- split.
----------- exact H2.
----------- split.
------------ exact H3.
------------ split.
------------- exact H6.
------------- split.
-------------- exact H7.
-------------- exact H8.
Qed.
