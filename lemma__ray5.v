Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__ray1.
Require Export lemma__ray4.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__ray5 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Out A B C) -> (euclidean__defs.Out A C B).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as H0.
- apply (@lemma__ray1.lemma__ray1 (A) (B) (C) H).
- assert (* Cut *) (euclidean__axioms.neq A C) as H1.
-- apply (@lemma__raystrict.lemma__raystrict (A) (B) (C) H).
-- assert (* Cut *) (euclidean__defs.Out A C B) as H2.
--- apply (@lemma__ray4.lemma__ray4 (A) (C) (B)).
----assert (euclidean__axioms.BetS A C B \/ (B = C) \/ (euclidean__axioms.BetS A B C)) as H2.
----- exact H0.
----- destruct H2 as [H2|H2].
------ right.
right.
exact H2.
------ assert (B = C \/ euclidean__axioms.BetS A B C) as H3.
------- exact H2.
------- destruct H3 as [H3|H3].
-------- right.
left.
exact H3.
-------- left.
exact H3.

----assert (euclidean__axioms.BetS A C B \/ (B = C) \/ (euclidean__axioms.BetS A B C)) as H2.
----- exact H0.
----- destruct H2 as [H2|H2].
------ exact H1.
------ assert (B = C \/ euclidean__axioms.BetS A B C) as H3.
------- exact H2.
------- destruct H3 as [H3|H3].
-------- exact H1.
-------- exact H1.

--- exact H2.
Qed.
