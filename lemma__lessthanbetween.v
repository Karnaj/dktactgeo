Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__layoffunique.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Definition lemma__lessthanbetween : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Lt A B A C) -> ((euclidean__defs.Out A B C) -> (euclidean__axioms.BetS A B C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M A B)) as H1.
- exact H.
- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M A B))) as H2.
-- exact H1.
-- destruct H2 as [M H2].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M A B)) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* Cut *) (euclidean__axioms.neq A M) as H5.
---- assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H5.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (C) H3).
----- assert (* AndElim *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
exact H8.
---- assert (* Cut *) (euclidean__defs.Out A M C) as H6.
----- apply (@lemma__ray4.lemma__ray4 (A) (M) (C)).
------right.
right.
exact H3.

------ exact H5.
----- assert (* Cut *) (euclidean__defs.Out A C M) as H7.
------ apply (@lemma__ray5.lemma__ray5 (A) (M) (C) H6).
------ assert (* Cut *) (euclidean__defs.Out A C B) as H8.
------- apply (@lemma__ray5.lemma__ray5 (A) (B) (C) H0).
------- assert (* Cut *) (M = B) as H9.
-------- apply (@lemma__layoffunique.lemma__layoffunique (A) (C) (M) (B) (H7) (H8) H4).
-------- assert (* Cut *) (euclidean__axioms.BetS A B C) as H10.
--------- apply (@eq__ind__r euclidean__axioms.Point B (fun M0: euclidean__axioms.Point => (euclidean__axioms.BetS A M0 C) -> ((euclidean__axioms.Cong A M0 A B) -> ((euclidean__axioms.neq A M0) -> ((euclidean__defs.Out A M0 C) -> ((euclidean__defs.Out A C M0) -> (euclidean__axioms.BetS A B C))))))) with (x := M).
----------intro H10.
intro H11.
intro H12.
intro H13.
intro H14.
exact H10.

---------- exact H9.
---------- exact H3.
---------- exact H4.
---------- exact H5.
---------- exact H6.
---------- exact H7.
--------- exact H10.
Qed.
