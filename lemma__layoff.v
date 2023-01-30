Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export logic.
Definition lemma__layoff : forall A B C D, (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq C D) -> (exists X, (euclidean__defs.Out A B X) /\ (euclidean__axioms.Cong A X C D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (~(B = A)) as H1.
- intro H1.
assert (* Cut *) (A = B) as H2.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric A B H1).
-- apply (@H H2).
- assert (* Cut *) (exists E, (euclidean__axioms.BetS B A E) /\ (euclidean__axioms.Cong A E C D)) as H2.
-- apply (@lemma__extension.lemma__extension B A C D H1 H0).
-- destruct H2 as [E H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.BetS E A B) as H6.
--- apply (@euclidean__axioms.axiom__betweennesssymmetry B A E H4).
--- assert (* Cut *) (euclidean__axioms.neq E A) as H7.
---- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))) as H7.
----- apply (@lemma__betweennotequal.lemma__betweennotequal E A B H6).
----- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H10.
---- assert (euclidean__axioms.BetS E A B) as H8 by exact H6.
assert (* Cut *) (exists P, (euclidean__axioms.BetS E A P) /\ (euclidean__axioms.Cong A P C D)) as H9.
----- apply (@lemma__extension.lemma__extension E A C D H7 H0).
----- destruct H9 as [P H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__defs.Out A B P) as H13.
------ exists E.
split.
------- exact H11.
------- exact H8.
------ exists P.
split.
------- exact H13.
------- exact H12.
Qed.
