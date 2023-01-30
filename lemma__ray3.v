Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__outerconnectivity.
Require Export logic.
Definition lemma__ray3 : forall B C D V, (euclidean__defs.Out B C D) -> ((euclidean__defs.Out B C V) -> (euclidean__defs.Out B D V)).
Proof.
intro B.
intro C.
intro D.
intro V.
intro H.
intro H0.
assert (exists E, (euclidean__axioms.BetS E B D) /\ (euclidean__axioms.BetS E B C)) as H1 by exact H.
destruct H1 as [E H2].
destruct H2 as [H3 H4].
assert (exists H5, (euclidean__axioms.BetS H5 B V) /\ (euclidean__axioms.BetS H5 B C)) as H5 by exact H0.
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert (* Cut *) (~(~(euclidean__axioms.BetS E B V))) as H10.
- intro H10.
assert (* Cut *) (~(euclidean__axioms.BetS B E H6)) as H11.
-- intro H11.
assert (* Cut *) (euclidean__axioms.BetS H6 E B) as H12.
--- apply (@euclidean__axioms.axiom__betweennesssymmetry B E H6 H11).
--- assert (* Cut *) (euclidean__axioms.BetS E B V) as H13.
---- apply (@lemma__3__6a.lemma__3__6a H6 E B V H12 H8).
---- apply (@H10 H13).
-- assert (* Cut *) (~(euclidean__axioms.BetS B H6 E)) as H12.
--- intro H12.
assert (* Cut *) (euclidean__axioms.BetS E H6 B) as H13.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry B H6 E H12).
---- assert (* Cut *) (euclidean__axioms.BetS E B V) as H14.
----- apply (@lemma__3__7a.lemma__3__7a E H6 B V H13 H8).
----- apply (@H10 H14).
--- assert (* Cut *) (euclidean__axioms.BetS C B E) as H13.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry E B C H4).
---- assert (* Cut *) (euclidean__axioms.BetS C B H6) as H14.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry H6 B C H9).
----- assert (* Cut *) (H6 = E) as H15.
------ apply (@lemma__outerconnectivity.lemma__outerconnectivity C B H6 E H14 H13 H12 H11).
------ assert (* Cut *) (euclidean__axioms.BetS E B V) as H16.
------- apply (@eq__ind__r euclidean__axioms.Point E (fun H16 => (euclidean__axioms.BetS H16 B V) -> ((euclidean__axioms.BetS H16 B C) -> ((~(euclidean__axioms.BetS B E H16)) -> ((~(euclidean__axioms.BetS B H16 E)) -> ((euclidean__axioms.BetS C B H16) -> (euclidean__axioms.BetS E B V))))))) with (x := H6).
--------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
exact H16.

-------- exact H15.
-------- exact H8.
-------- exact H9.
-------- exact H11.
-------- exact H12.
-------- exact H14.
------- apply (@H10 H16).
- assert (* Cut *) (euclidean__defs.Out B D V) as H11.
-- assert (* Cut *) (euclidean__axioms.BetS E B V) as H11.
--- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E B V) H10).
--- exists E.
split.
---- exact H11.
---- exact H3.
-- exact H11.
Qed.
