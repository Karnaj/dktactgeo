Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__parallelNC : forall A B C D, (euclidean__defs.Par A B C D) -> ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists M a b c d, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))))))) as H0.
- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H0 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [x2 H4].
destruct H4 as [x3 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exists x3.
exists x.
exists x0.
exists x1.
exists x2.
split.
-- exact H6.
-- split.
--- exact H8.
--- split.
---- exact H10.
---- split.
----- exact H12.
----- split.
------ exact H14.
------ split.
------- exact H16.
------- split.
-------- exact H18.
-------- split.
--------- exact H20.
--------- split.
---------- exact H22.
---------- split.
----------- exact H24.
----------- exact H25.
- destruct H0 as [M H1].
destruct H1 as [a H2].
destruct H2 as [b H3].
destruct H3 as [c H4].
destruct H4 as [d H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (~(euclidean__axioms.Col A C D)) as H26.
-- intro H26.
assert (* Cut *) (euclidean__axioms.Col C D A) as H27.
--- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H27.
---- apply (@lemma__collinearorder.lemma__collinearorder A C D H26).
---- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H30.
--- assert (* Cut *) (A = A) as H28.
---- apply (@logic.eq__refl Point A).
---- assert (* Cut *) (euclidean__axioms.Col A B A) as H29.
----- right.
left.
exact H28.
----- assert (* Cut *) (euclidean__defs.Meet A B C D) as H30.
------ exists A.
split.
------- exact H6.
------- split.
-------- exact H8.
-------- split.
--------- exact H29.
--------- exact H27.
------ apply (@H22 H30).
-- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H27.
--- intro H27.
assert (* Cut *) (C = C) as H28.
---- apply (@logic.eq__refl Point C).
---- assert (* Cut *) (euclidean__axioms.Col C D C) as H29.
----- right.
left.
exact H28.
----- assert (* Cut *) (euclidean__defs.Meet A B C D) as H30.
------ exists C.
split.
------- exact H6.
------- split.
-------- exact H8.
-------- split.
--------- exact H27.
--------- exact H29.
------ apply (@H22 H30).
--- assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H28.
---- intro H28.
assert (* Cut *) (euclidean__axioms.Col C D B) as H29.
----- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H29.
------ apply (@lemma__collinearorder.lemma__collinearorder B C D H28).
------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
----- assert (* Cut *) (B = B) as H30.
------ apply (@logic.eq__refl Point B).
------ assert (* Cut *) (euclidean__axioms.Col A B B) as H31.
------- right.
right.
left.
exact H30.
------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H32.
-------- exists B.
split.
--------- exact H6.
--------- split.
---------- exact H8.
---------- split.
----------- exact H31.
----------- exact H29.
-------- apply (@H22 H32).
---- assert (* Cut *) (~(euclidean__axioms.Col A B D)) as H29.
----- intro H29.
assert (* Cut *) (D = D) as H30.
------ apply (@logic.eq__refl Point D).
------ assert (* Cut *) (euclidean__axioms.Col C D D) as H31.
------- right.
right.
left.
exact H30.
------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H32.
-------- exists D.
split.
--------- exact H6.
--------- split.
---------- exact H8.
---------- split.
----------- exact H29.
----------- exact H31.
-------- apply (@H22 H32).
----- split.
------ apply (@euclidean__tactics.nCol__notCol A B C H27).
------ split.
------- apply (@euclidean__tactics.nCol__notCol A C D H26).
------- split.
-------- apply (@euclidean__tactics.nCol__notCol B C D H28).
-------- apply (@euclidean__tactics.nCol__notCol A B D H29).
Qed.
