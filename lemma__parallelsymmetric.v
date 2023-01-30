Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Definition lemma__parallelsymmetric : forall A B C D, (euclidean__defs.Par A B C D) -> (euclidean__defs.Par C D A B).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (exists a b c d m, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H0 by exact H.
destruct H0 as [a H1].
destruct H1 as [b H2].
destruct H2 as [c H3].
destruct H3 as [d H4].
destruct H4 as [m H5].
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
assert (* Cut *) (~(euclidean__defs.Meet C D A B)) as H26.
- intro H26.
assert (exists P, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P)))) as H27 by exact H26.
destruct H27 as [P H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
assert (* Cut *) (euclidean__defs.Meet A B C D) as H35.
-- exists P.
split.
--- exact H31.
--- split.
---- exact H29.
---- split.
----- exact H34.
----- exact H33.
-- apply (@H22 H35).
- assert (* Cut *) (euclidean__defs.Par C D A B) as H27.
-- exists c.
exists d.
exists a.
exists b.
exists m.
split.
--- exact H8.
--- split.
---- exact H6.
---- split.
----- exact H16.
----- split.
------ exact H18.
------ split.
------- exact H20.
------- split.
-------- exact H10.
-------- split.
--------- exact H12.
--------- split.
---------- exact H14.
---------- split.
----------- exact H26.
----------- split.
------------ exact H25.
------------ exact H24.
-- exact H27.
Qed.
