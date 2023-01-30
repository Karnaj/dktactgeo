Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__3__6b.
Require Export lemma__congruencesymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__partnotequalwhole.
Require Export logic.
Definition lemma__trichotomy2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Lt A B C D) -> (~(euclidean__defs.Lt C D A B)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS C E D) /\ (euclidean__axioms.Cong C E A B)) as H0.
- exact H.
- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS C E D) /\ (euclidean__axioms.Cong C E A B))) as H1.
-- exact H0.
-- destruct H1 as [E H1].
assert (* AndElim *) ((euclidean__axioms.BetS C E D) /\ (euclidean__axioms.Cong C E A B)) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* Cut *) (euclidean__axioms.Cong A B C E) as H4.
---- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (C) (E) (B) H3).
---- assert (* Cut *) (~(euclidean__defs.Lt C D A B)) as H5.
----- intro H5.
assert (* Cut *) (euclidean__defs.Lt C D C E) as H6.
------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (D) (A) (B) (C) (E) (H5) H4).
------ assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong C F C D)) as H7.
------- exact H6.
------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong C F C D))) as H8.
-------- exact H7.
-------- destruct H8 as [F H8].
assert (* AndElim *) ((euclidean__axioms.BetS C F E) /\ (euclidean__axioms.Cong C F C D)) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__axioms.BetS C F D) as H11.
---------- apply (@lemma__3__6b.lemma__3__6b (C) (F) (E) (D) (H9) H2).
---------- assert (* Cut *) (~(euclidean__axioms.Cong C F C D)) as H12.
----------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (C) (F) (D) H11).
----------- apply (@H12 H10).
----- exact H5.
Qed.
