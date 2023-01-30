Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Require Export proposition__02.
Definition lemma__extension : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.neq P Q) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ (euclidean__axioms.Cong B X P Q))).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro H.
intro H0.
assert (* Cut *) (B = B) as H1.
- apply (@logic.eq__refl (Point) B).
- assert (* Cut *) (exists (D: euclidean__axioms.Point), euclidean__axioms.Cong B D P Q) as H2.
-- assert (* Cut *) ((B = P) \/ (euclidean__axioms.neq B P)) as H2.
--- apply (@euclidean__tactics.eq__or__neq (B) P).
--- assert (* Cut *) ((B = P) \/ (euclidean__axioms.neq B P)) as H3.
---- exact H2.
---- assert (* Cut *) ((B = P) \/ (euclidean__axioms.neq B P)) as __TmpHyp.
----- exact H3.
----- assert (B = P \/ euclidean__axioms.neq B P) as H4.
------ exact __TmpHyp.
------ destruct H4 as [H4|H4].
------- assert (* Cut *) (euclidean__axioms.neq Q P) as H5.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (Q) H0).
-------- assert (* Cut *) (euclidean__axioms.neq Q B) as H6.
--------- apply (@eq__ind__r euclidean__axioms.Point P (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((B0 = B0) -> (euclidean__axioms.neq Q B0)))) with (x := B).
----------intro H6.
intro H7.
exact H5.

---------- exact H4.
---------- exact H.
---------- exact H1.
--------- assert (* Cut *) (euclidean__axioms.neq B Q) as H7.
---------- apply (@eq__ind__r euclidean__axioms.Point P (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((B0 = B0) -> ((euclidean__axioms.neq Q B0) -> (euclidean__axioms.neq B0 Q))))) with (x := B).
-----------intro H7.
intro H8.
intro H9.
exact H0.

----------- exact H4.
----------- exact H.
----------- exact H1.
----------- exact H6.
---------- assert (* Cut *) (exists (D: euclidean__axioms.Point), euclidean__axioms.Cong B D Q P) as H8.
----------- apply (@proposition__02.proposition__02 (B) (Q) (P) (H7) H5).
----------- assert (exists D: euclidean__axioms.Point, (euclidean__axioms.Cong B D Q P)) as H9.
------------ exact H8.
------------ destruct H9 as [D H9].
assert (* Cut *) (euclidean__axioms.Cong B D P Q) as H10.
------------- assert (* Cut *) ((euclidean__axioms.Cong D B P Q) /\ ((euclidean__axioms.Cong D B Q P) /\ (euclidean__axioms.Cong B D P Q))) as H10.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (D) (Q) (P) H9).
-------------- assert (* AndElim *) ((euclidean__axioms.Cong D B P Q) /\ ((euclidean__axioms.Cong D B Q P) /\ (euclidean__axioms.Cong B D P Q))) as H11.
--------------- exact H10.
--------------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Cong D B Q P) /\ (euclidean__axioms.Cong B D P Q)) as H13.
---------------- exact H12.
---------------- destruct H13 as [H13 H14].
exact H14.
------------- exists D.
exact H10.
------- assert (* Cut *) (exists (D: euclidean__axioms.Point), euclidean__axioms.Cong B D P Q) as H5.
-------- apply (@proposition__02.proposition__02 (B) (P) (Q) (H4) H0).
-------- assert (exists D: euclidean__axioms.Point, (euclidean__axioms.Cong B D P Q)) as H6.
--------- exact H5.
--------- destruct H6 as [D H6].
exists D.
exact H6.
-- assert (exists D: euclidean__axioms.Point, (euclidean__axioms.Cong B D P Q)) as H3.
--- exact H2.
--- destruct H3 as [D H3].
assert (* Cut *) (euclidean__axioms.Cong P Q B D) as H4.
---- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (P) (B) (D) (Q) H3).
---- assert (* Cut *) (euclidean__axioms.neq B D) as H5.
----- apply (@euclidean__axioms.axiom__nocollapse (P) (Q) (B) (D) (H0) H4).
----- assert (* Cut *) (exists (J: euclidean__axioms.Circle), euclidean__axioms.CI J B B D) as H6.
------ apply (@euclidean__axioms.postulate__Euclid3 (B) (D) H5).
------ assert (exists J: euclidean__axioms.Circle, (euclidean__axioms.CI J B B D)) as H7.
------- exact H6.
------- destruct H7 as [J H7].
assert (* Cut *) (euclidean__axioms.InCirc B J) as H8.
-------- exists A.
exists A.
exists B.
exists B.
exists D.
split.
--------- exact H7.
--------- left.
exact H1.
-------- assert (* Cut *) (exists (C: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))))) as H9.
--------- apply (@euclidean__axioms.postulate__line__circle (A) (B) (B) (J) (B) (D) (H7) (H8) H).
--------- assert (exists C: euclidean__axioms.Point, (exists (E: euclidean__axioms.Point), (euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))))) as H10.
---------- exact H9.
---------- destruct H10 as [C H10].
assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))))) as H11.
----------- exact H10.
----------- destruct H11 as [E H11].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.OnCirc C J) /\ ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.OnCirc E J) /\ (euclidean__axioms.BetS C B E)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.Cong B E B D) as H20.
---------------- apply (@euclidean__axioms.axiom__circle__center__radius (B) (B) (D) (J) (E) (H7) H18).
---------------- assert (* Cut *) (euclidean__axioms.Cong B E P Q) as H21.
----------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (E) (B) (D) (P) (Q) (H20) H3).
----------------- exists E.
split.
------------------ exact H14.
------------------ exact H21.
Qed.
