Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__lessthannotequal : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Lt A B C D) -> ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq C D)).
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
assert (* Cut *) (euclidean__axioms.neq C E) as H4.
---- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H4.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (D) H2).
----- assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
exact H7.
---- assert (* Cut *) (euclidean__axioms.neq A B) as H5.
----- apply (@euclidean__axioms.axiom__nocollapse (C) (E) (A) (B) (H4) H3).
----- assert (* Cut *) (euclidean__axioms.neq C D) as H6.
------ assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H6.
------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (E) (D) H2).
------- assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ (euclidean__axioms.neq C D)) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
exact H10.
------ split.
------- exact H5.
------- exact H6.
Qed.
