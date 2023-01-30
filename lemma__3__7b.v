Require Export euclidean__axioms.
Require Export lemma__3__7a.
Definition lemma__3__7b : forall A B C D, (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS B C D) -> (euclidean__axioms.BetS A B D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.BetS C B A) as H1.
- apply (@euclidean__axioms.axiom__betweennesssymmetry A B C H).
- assert (* Cut *) (euclidean__axioms.BetS D C B) as H2.
-- apply (@euclidean__axioms.axiom__betweennesssymmetry B C D H0).
-- assert (* Cut *) (euclidean__axioms.BetS D B A) as H3.
--- apply (@lemma__3__7a.lemma__3__7a D C B A H2 H1).
--- assert (* Cut *) (euclidean__axioms.BetS A B D) as H4.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry D B A H3).
---- exact H4.
Qed.
