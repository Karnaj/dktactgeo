Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__05.
Definition proposition__05b : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__defs.isosceles A B C) -> ((euclidean__axioms.BetS A B F) -> ((euclidean__axioms.BetS A C G) -> (euclidean__defs.CongA C B F B C G))).
Proof.
intro A.
intro B.
intro C.
intro F.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__defs.CongA A B C A C B) as H2.
- apply (@proposition__05.proposition__05 (A) (B) (C) H).
- assert (* Cut *) (C = C) as H3.
-- apply (@logic.eq__refl (Point) C).
-- assert (* Cut *) (euclidean__axioms.nCol A C B) as H4.
--- apply (@euclidean__tactics.nCol__notCol (A) (C) (B)).
----apply (@euclidean__tactics.nCol__not__Col (A) (C) (B)).
-----apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (A) (C) (B) H2).


--- assert (* Cut *) (~(B = C)) as H5.
---- intro H5.
assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
----- right.
right.
left.
exact H5.
----- assert (* Cut *) (euclidean__axioms.Col A C B) as H7.
------ assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H7.
------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H6).
------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H14.
------ apply (@euclidean__tactics.Col__nCol__False (A) (C) (B) (H4) H7).
---- assert (* Cut *) (euclidean__axioms.neq C B) as H6.
----- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H5).
----- assert (* Cut *) (euclidean__defs.Out B C C) as H7.
------ apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
-------right.
left.
exact H3.

------- exact H5.
------ assert (* Cut *) (euclidean__defs.Supp A B C C F) as H8.
------- split.
-------- exact H7.
-------- exact H0.
------- assert (* Cut *) (B = B) as H9.
-------- apply (@logic.eq__refl (Point) B).
-------- assert (* Cut *) (euclidean__defs.Out C B B) as H10.
--------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
----------right.
left.
exact H9.

---------- exact H6.
--------- assert (* Cut *) (euclidean__defs.Supp A C B B G) as H11.
---------- split.
----------- exact H10.
----------- exact H1.
---------- assert (* Cut *) (euclidean__defs.CongA C B F B C G) as H12.
----------- apply (@lemma__supplements.lemma__supplements (A) (B) (C) (C) (F) (A) (C) (B) (B) (G) (H2) (H8) H11).
----------- exact H12.
Qed.
