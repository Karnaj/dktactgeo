Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__lessthannotequal : forall A B C D, (euclidean__defs.Lt A B C D) -> ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (exists E, (euclidean__axioms.BetS C E D) /\ (euclidean__axioms.Cong C E A B)) as H0 by exact H.
destruct H0 as [E H1].
destruct H1 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq C E) as H4.
- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H4.
-- apply (@lemma__betweennotequal.lemma__betweennotequal C E D H2).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H7.
- assert (* Cut *) (euclidean__axioms.neq A B) as H5.
-- apply (@euclidean__axioms.axiom__nocollapse C E A B H4 H3).
-- assert (* Cut *) (euclidean__axioms.neq C D) as H6.
--- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H6.
---- apply (@lemma__betweennotequal.lemma__betweennotequal C E D H2).
---- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H10.
--- split.
---- exact H5.
---- exact H6.
Qed.
