Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__3__7b.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export logic.
Definition lemma__ray4 : forall A B E, ((euclidean__axioms.BetS A E B) \/ ((E = B) \/ (euclidean__axioms.BetS A B E))) -> ((euclidean__axioms.neq A B) -> (euclidean__defs.Out A B E)).
Proof.
intro A.
intro B.
intro E.
intro H.
intro H0.
assert (* Cut *) (~(B = A)) as H1.
- intro H1.
assert (* Cut *) (A = B) as H2.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric A B H1).
-- apply (@H0 H2).
- assert (* Cut *) (exists J, (euclidean__axioms.BetS B A J) /\ (euclidean__axioms.Cong A J A B)) as H2.
-- apply (@lemma__extension.lemma__extension B A A B H1 H0).
-- destruct H2 as [J H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.BetS J A B) as H6.
--- apply (@euclidean__axioms.axiom__betweennesssymmetry B A J H4).
--- assert (* Cut *) (euclidean__defs.Out A B E) as H7.
---- assert ((euclidean__axioms.BetS A E B) \/ ((E = B) \/ (euclidean__axioms.BetS A B E))) as H7 by exact H.
assert ((euclidean__axioms.BetS A E B) \/ ((E = B) \/ (euclidean__axioms.BetS A B E))) as __TmpHyp by exact H7.
destruct __TmpHyp as [H8|H8].
----- assert (* Cut *) (euclidean__axioms.BetS J A E) as H9.
------ apply (@euclidean__axioms.axiom__innertransitivity J A E B H6 H8).
------ assert (* Cut *) (euclidean__defs.Out A B E) as H10.
------- exists J.
split.
-------- exact H9.
-------- exact H6.
------- exact H10.
----- destruct H8 as [H9|H9].
------ assert (* Cut *) (euclidean__axioms.BetS J A E) as H10.
------- apply (@eq__ind__r euclidean__axioms.Point B (fun E0 => euclidean__axioms.BetS J A E0)) with (x := E).
-------- exact H6.
-------- exact H9.
------- assert (* Cut *) (euclidean__defs.Out A B E) as H11.
-------- exists J.
split.
--------- exact H10.
--------- exact H6.
-------- exact H11.
------ assert (* Cut *) (euclidean__axioms.BetS J A E) as H10.
------- apply (@lemma__3__7b.lemma__3__7b J A B E H6 H9).
------- assert (* Cut *) (euclidean__defs.Out A B E) as H11.
-------- exists J.
split.
--------- exact H10.
--------- exact H6.
-------- exact H11.
---- exact H7.
Qed.
