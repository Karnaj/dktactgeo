Require Export euclidean__axioms.
Definition lemma__3__6a : forall A B C D, (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS A C D) -> (euclidean__axioms.BetS B C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.BetS C B A) as H1.
- apply (@euclidean__axioms.axiom__betweennesssymmetry A B C H).
- assert (* Cut *) (euclidean__axioms.BetS D C A) as H2.
-- apply (@euclidean__axioms.axiom__betweennesssymmetry A C D H0).
-- assert (* Cut *) (euclidean__axioms.BetS D C B) as H3.
--- apply (@euclidean__axioms.axiom__innertransitivity D C B A H2 H1).
--- assert (* Cut *) (euclidean__axioms.BetS B C D) as H4.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry D C B H3).
---- exact H4.
Qed.
