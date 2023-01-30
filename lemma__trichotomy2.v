Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__3__6b.
Require Export lemma__congruencesymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__partnotequalwhole.
Require Export logic.
Definition lemma__trichotomy2 : forall A B C D, (euclidean__defs.Lt A B C D) -> (~(euclidean__defs.Lt C D A B)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (exists E, (euclidean__axioms.BetS C E D) /\ (euclidean__axioms.Cong C E A B)) as H0 by exact H.
destruct H0 as [E H1].
destruct H1 as [H2 H3].
assert (* Cut *) (euclidean__axioms.Cong A B C E) as H4.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A C E B H3).
- assert (* Cut *) (~(euclidean__defs.Lt C D A B)) as H5.
-- intro H5.
assert (* Cut *) (euclidean__defs.Lt C D C E) as H6.
--- apply (@lemma__lessthancongruence.lemma__lessthancongruence C D A B C E H5 H4).
--- assert (exists F, (euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong C F C D)) as H7 by exact H6.
destruct H7 as [F H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__axioms.BetS C F D) as H11.
---- apply (@lemma__3__6b.lemma__3__6b C F E D H9 H2).
---- assert (* Cut *) (~(euclidean__axioms.Cong C F C D)) as H12.
----- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole C F D H11).
----- apply (@H12 H10).
-- exact H5.
Qed.
