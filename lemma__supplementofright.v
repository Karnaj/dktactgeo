Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__betweennotequal.
Require Export lemma__collinearright.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__supplementofright : forall A B C D F, (euclidean__defs.Supp A B C D F) -> ((euclidean__defs.Per A B C) -> ((euclidean__defs.Per F B D) /\ (euclidean__defs.Per D B F))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro F.
intro H.
intro H0.
assert (* Cut *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H1.
- assert ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H1 by exact H.
assert ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as __TmpHyp by exact H1.
destruct __TmpHyp as [H2 H3].
split.
-- exact H2.
-- exact H3.
- assert (* Cut *) (euclidean__axioms.Col A B F) as H2.
-- destruct H1 as [H2 H3].
right.
right.
right.
right.
left.
exact H3.
-- assert (* Cut *) (euclidean__axioms.neq B F) as H3.
--- destruct H1 as [H3 H4].
assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H5.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A B F H4).
---- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H6.
--- assert (* Cut *) (euclidean__axioms.neq F B) as H4.
---- destruct H1 as [H4 H5].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B F H3).
---- assert (* Cut *) (euclidean__defs.Per F B C) as H5.
----- destruct H1 as [H5 H6].
apply (@lemma__collinearright.lemma__collinearright A B F C H0 H2 H4).
----- assert (* Cut *) (euclidean__defs.Per F B D) as H6.
------ destruct H1 as [H6 H7].
apply (@lemma__8__3.lemma__8__3 F B C D H5 H6).
------ assert (* Cut *) (euclidean__defs.Per D B F) as H7.
------- destruct H1 as [H7 H8].
apply (@lemma__8__2.lemma__8__2 F B D H6).
------- split.
-------- exact H6.
-------- exact H7.
Qed.
