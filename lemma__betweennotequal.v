Require Export euclidean__axioms.
Require Export lemma__3__6a.
Require Export logic.
Definition lemma__betweennotequal : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(B = C)) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.BetS A C B) as H1.
-- apply (@eq__ind__r euclidean__axioms.Point C (fun B0: euclidean__axioms.Point => (euclidean__axioms.BetS A B0 C) -> (euclidean__axioms.BetS A C B0))) with (x := B).
---intro H1.
exact H1.

--- exact H0.
--- exact H.
-- assert (* Cut *) (euclidean__axioms.BetS B C B) as H2.
--- apply (@lemma__3__6a.lemma__3__6a (A) (B) (C) (B) (H) H1).
--- assert (* Cut *) (~(euclidean__axioms.BetS B C B)) as H3.
---- apply (@euclidean__axioms.axiom__betweennessidentity (B) C).
---- apply (@H3 H2).
- assert (* Cut *) (~(A = B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.BetS B A C) as H2.
--- apply (@eq__ind__r euclidean__axioms.Point B (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 B C) -> (euclidean__axioms.BetS B A0 C))) with (x := A).
----intro H2.
exact H2.

---- exact H1.
---- exact H.
--- assert (* Cut *) (euclidean__axioms.BetS A B A) as H3.
---- apply (@euclidean__axioms.axiom__innertransitivity (A) (B) (A) (C) (H) H2).
---- assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H4.
----- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
----- apply (@H4 H3).
-- assert (* Cut *) (~(A = C)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.BetS A B A) as H3.
---- apply (@eq__ind__r euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 B C) -> ((~(A0 = B)) -> (euclidean__axioms.BetS A0 B A0)))) with (x := A).
-----intro H3.
intro H4.
exact H3.

----- exact H2.
----- exact H.
----- exact H1.
---- assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H4.
----- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
----- apply (@H4 H3).
--- split.
---- exact H0.
---- split.
----- exact H1.
----- exact H2.
Qed.
