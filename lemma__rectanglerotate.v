Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Definition lemma__rectanglerotate : forall A B C D, (euclidean__defs.RE A B C D) -> (euclidean__defs.RE B C D A).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0.
- assert ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0 by exact H.
assert ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
split.
-- exact H1.
-- split.
--- exact H3.
--- split.
---- exact H5.
---- split.
----- exact H7.
----- exact H8.
- assert (* Cut *) (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H1.
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H8.
-- destruct H1 as [M H2].
destruct H2 as [H3 H4].
destruct H0 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__axioms.BetS C M A) as H13.
--- apply (@euclidean__axioms.axiom__betweennesssymmetry A M C H3).
--- assert (* Cut *) (euclidean__defs.CR B D C A) as H14.
---- exists M.
split.
----- exact H4.
----- exact H13.
---- assert (* Cut *) (euclidean__defs.RE B C D A) as H15.
----- split.
------ exact H7.
------ split.
------- exact H9.
------- split.
-------- exact H11.
-------- split.
--------- exact H5.
--------- exact H14.
----- exact H15.
Qed.
