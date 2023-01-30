Require Export euclidean__axioms.
Require Export logic.
Definition lemma__localextension : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq B Q) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ (euclidean__axioms.Cong B X B Q))).
Proof.
intro A.
intro B.
intro Q.
intro H.
intro H0.
assert (* Cut *) (B = B) as H1.
- apply (@logic.eq__refl (Point) B).
- assert (* Cut *) (exists (J: euclidean__axioms.Circle), euclidean__axioms.CI J B B Q) as H2.
-- apply (@euclidean__axioms.postulate__Euclid3 (B) (Q) H0).
-- assert (exists J: euclidean__axioms.Circle, (euclidean__axioms.CI J B B Q)) as H3.
--- exact H2.
--- destruct H3 as [J H3].
assert (* Cut *) (euclidean__axioms.InCirc B J) as H4.
---- exists A.
exists A.
exists B.
exists B.
exists Q.
split.
----- exact H3.
----- left.
exact H1.
---- assert (* Cut *) (exists (C: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))))) as H5.
----- apply (@euclidean__axioms.postulate__line__circle (A) (B) (B) (J) (B) (Q) (H3) (H4) H).
----- assert (exists C: euclidean__axioms.Point, (exists (E: euclidean__axioms.Point), (euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))))) as H6.
------ exact H5.
------ destruct H6 as [C H6].
assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))))) as H7.
------- exact H6.
------- destruct H7 as [E H7].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.Cong B E B Q) as H16.
------------ apply (@euclidean__axioms.axiom__circle__center__radius (B) (B) (Q) (J) (E) (H3) H14).
------------ exists E.
split.
------------- exact H10.
------------- exact H16.
Qed.
