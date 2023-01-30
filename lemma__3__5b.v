Require Export euclidean__axioms.
Require Export lemma__3__7a.
Definition lemma__3__5b : forall A B C D, (euclidean__axioms.BetS A B D) -> ((euclidean__axioms.BetS B C D) -> (euclidean__axioms.BetS A C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.BetS A B C) as H1.
- apply (@euclidean__axioms.axiom__innertransitivity A B C D H H0).
- assert (* Cut *) (euclidean__axioms.BetS A C D) as H2.
-- apply (@lemma__3__7a.lemma__3__7a A B C D H1 H0).
-- exact H2.
Qed.
