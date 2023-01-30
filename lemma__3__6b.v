Require Export euclidean__axioms.
Require Export lemma__3__5b.
Definition lemma__3__6b : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS A C D) -> (euclidean__axioms.BetS A B D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.BetS C B A) as H1.
- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (C) H).
- assert (* Cut *) (euclidean__axioms.BetS D C A) as H2.
-- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (C) (D) H0).
-- assert (* Cut *) (euclidean__axioms.BetS D B A) as H3.
--- apply (@lemma__3__5b.lemma__3__5b (D) (C) (B) (A) (H2) H1).
--- assert (* Cut *) (euclidean__axioms.BetS A B D) as H4.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (B) (A) H3).
---- exact H4.
Qed.
