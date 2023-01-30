Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__equalitysymmetric.
Require Export lemma__parallelcollinear1.
Require Export lemma__parallelcollinear2.
Require Export lemma__tarskiparallelflip.
Require Export logic.
Definition lemma__parallelcollinear : forall A B C c d, (euclidean__defs.TP A B c d) -> ((euclidean__axioms.Col c d C) -> ((euclidean__axioms.neq C d) -> (euclidean__defs.TP A B C d))).
Proof.
intro A.
intro B.
intro C.
intro c.
intro d.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H2.
- assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H2 by exact H.
assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as __TmpHyp by exact H2.
destruct __TmpHyp as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
split.
-- exact H3.
-- split.
--- exact H5.
--- split.
---- exact H7.
---- exact H8.
- assert (* Cut *) ((c = d) \/ ((c = C) \/ ((d = C) \/ ((euclidean__axioms.BetS d c C) \/ ((euclidean__axioms.BetS c d C) \/ (euclidean__axioms.BetS c C d)))))) as H3.
-- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H0.
-- assert (* Cut *) (euclidean__defs.TP A B C d) as H4.
--- assert ((c = d) \/ ((c = C) \/ ((d = C) \/ ((euclidean__axioms.BetS d c C) \/ ((euclidean__axioms.BetS c d C) \/ (euclidean__axioms.BetS c C d)))))) as H4 by exact H3.
assert ((c = d) \/ ((c = C) \/ ((d = C) \/ ((euclidean__axioms.BetS d c C) \/ ((euclidean__axioms.BetS c d C) \/ (euclidean__axioms.BetS c C d)))))) as __TmpHyp by exact H4.
destruct __TmpHyp as [H5|H5].
---- assert (* Cut *) (~(~(euclidean__defs.TP A B C d))) as H6.
----- intro H6.
destruct H2 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
apply (@H9 H5).
----- apply (@euclidean__tactics.NNPP (euclidean__defs.TP A B C d)).
------intro H7.
destruct H2 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
assert (* Cut *) (False) as H14.
------- apply (@H10 H5).
------- assert (* Cut *) (False) as H15.
-------- apply (@H6 H7).
-------- contradiction H15.

---- destruct H5 as [H6|H6].
----- assert (* Cut *) (euclidean__defs.TP A B C d) as H7.
------ destruct H2 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
apply (@eq__ind__r euclidean__axioms.Point C (fun c0 => (euclidean__defs.TP A B c0 d) -> ((euclidean__axioms.Col c0 d C) -> ((euclidean__axioms.neq c0 d) -> ((~(euclidean__defs.Meet A B c0 d)) -> ((euclidean__defs.OS c0 d A B) -> (euclidean__defs.TP A B C d))))))) with (x := c).
-------intro H13.
intro H14.
intro H15.
intro H16.
intro H17.
exact H13.

------- exact H6.
------- exact H.
------- exact H0.
------- exact H9.
------- exact H11.
------- exact H12.
------ exact H7.
----- destruct H6 as [H7|H7].
------ assert (* Cut *) (~(~(euclidean__defs.TP A B C d))) as H8.
------- intro H8.
assert (* Cut *) (C = d) as H9.
-------- destruct H2 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
apply (@lemma__equalitysymmetric.lemma__equalitysymmetric C d H7).
-------- apply (@H1 H9).
------- apply (@euclidean__tactics.NNPP (euclidean__defs.TP A B C d)).
--------intro H9.
destruct H2 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
assert (* Cut *) (False) as H16.
--------- apply (@H8 H9).
--------- contradiction H16.

------ destruct H7 as [H8|H8].
------- assert (* Cut *) (euclidean__axioms.BetS C c d) as H9.
-------- destruct H2 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
apply (@euclidean__axioms.axiom__betweennesssymmetry d c C H8).
-------- assert (* Cut *) (euclidean__defs.TP A B C d) as H10.
--------- destruct H2 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
apply (@lemma__parallelcollinear1.lemma__parallelcollinear1 A B C c d H H9).
--------- exact H10.
------- destruct H8 as [H9|H9].
-------- assert (* Cut *) (euclidean__axioms.BetS C d c) as H10.
--------- destruct H2 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
apply (@euclidean__axioms.axiom__betweennesssymmetry c d C H9).
--------- assert (* Cut *) (euclidean__defs.TP A B d c) as H11.
---------- destruct H2 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
assert (* Cut *) ((euclidean__defs.TP B A c d) /\ ((euclidean__defs.TP A B d c) /\ (euclidean__defs.TP B A d c))) as H17.
----------- apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B c d H).
----------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H20.
---------- assert (* Cut *) (euclidean__defs.TP A B C c) as H12.
----------- destruct H2 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
apply (@lemma__parallelcollinear1.lemma__parallelcollinear1 A B C d c H11 H10).
----------- assert (* Cut *) (euclidean__defs.TP A B c C) as H13.
------------ destruct H2 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
assert (* Cut *) ((euclidean__defs.TP B A C c) /\ ((euclidean__defs.TP A B c C) /\ (euclidean__defs.TP B A c C))) as H19.
------------- apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B C c H12).
------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H22.
------------ assert (* Cut *) (euclidean__defs.TP A B d C) as H14.
------------- destruct H2 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
apply (@lemma__parallelcollinear2.lemma__parallelcollinear2 A B d c C H13 H9).
------------- assert (* Cut *) (euclidean__defs.TP A B C d) as H15.
-------------- destruct H2 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
assert (* Cut *) ((euclidean__defs.TP B A d C) /\ ((euclidean__defs.TP A B C d) /\ (euclidean__defs.TP B A C d))) as H21.
--------------- apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B d C H14).
--------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
-------------- exact H15.
-------- assert (* Cut *) (euclidean__defs.TP A B C d) as H10.
--------- destruct H2 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
apply (@lemma__parallelcollinear2.lemma__parallelcollinear2 A B C c d H H9).
--------- exact H10.
--- exact H4.
Qed.
