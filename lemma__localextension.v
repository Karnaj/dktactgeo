Require Export euclidean__axioms.
Require Export logic.
Definition lemma__localextension : forall A B Q, (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq B Q) -> (exists X, (euclidean__axioms.BetS A B X) /\ (euclidean__axioms.Cong B X B Q))).
Proof.
intro A.
intro B.
intro Q.
intro H.
intro H0.
assert (* Cut *) (B = B) as H1.
- apply (@logic.eq__refl Point B).
- assert (* Cut *) (exists J, euclidean__axioms.CI J B B Q) as H2.
-- apply (@euclidean__axioms.postulate__Euclid3 B Q H0).
-- destruct H2 as [J H3].
assert (* Cut *) (euclidean__axioms.InCirc B J) as H4.
--- exists A.
exists A.
exists B.
exists B.
exists Q.
split.
---- exact H3.
---- left.
exact H1.
--- assert (* Cut *) (exists C E, (euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))))) as H5.
---- apply (@euclidean__axioms.postulate__line__circle A B B J B Q H3 H4 H).
---- destruct H5 as [C H6].
destruct H6 as [E H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.Cong B E B Q) as H16.
----- apply (@euclidean__axioms.axiom__circle__center__radius B B Q J E H3 H14).
----- exists E.
split.
------ exact H10.
------ exact H16.
Qed.
