Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__samesidereflexive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (P: euclidean__axioms.Point), (euclidean__axioms.nCol A B P) -> (euclidean__defs.OS P P A B).
Proof.
intro A.
intro B.
intro P.
intro H.
assert (* Cut *) (A = A) as H0.
- apply (@logic.eq__refl (Point) A).
- assert (* Cut *) (~(P = A)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col A B A) as H2.
--- right.
left.
exact H0.
--- assert (* Cut *) (euclidean__axioms.Col A B P) as H3.
---- apply (@eq__ind__r euclidean__axioms.Point A (fun P0: euclidean__axioms.Point => (euclidean__axioms.nCol A B P0) -> (euclidean__axioms.Col A B P0))) with (x := P).
-----intro H3.
exact H2.

----- exact H1.
----- exact H.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (P) (H) H3).
-- assert (* Cut *) (euclidean__axioms.neq A P) as H2.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (A) H1).
--- assert (* Cut *) (exists (C: euclidean__axioms.Point), (euclidean__axioms.BetS P A C) /\ (euclidean__axioms.Cong A C A P)) as H3.
---- apply (@lemma__extension.lemma__extension (P) (A) (A) (P) (H1) H2).
---- assert (exists C: euclidean__axioms.Point, ((euclidean__axioms.BetS P A C) /\ (euclidean__axioms.Cong A C A P))) as H4.
----- exact H3.
----- destruct H4 as [C H4].
assert (* AndElim *) ((euclidean__axioms.BetS P A C) /\ (euclidean__axioms.Cong A C A P)) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Col A B A) as H7.
------- right.
left.
exact H0.
------- assert (* Cut *) (euclidean__defs.OS P P A B) as H8.
-------- exists C.
exists A.
exists A.
split.
--------- exact H7.
--------- split.
---------- exact H7.
---------- split.
----------- exact H5.
----------- split.
------------ exact H5.
------------ split.
------------- exact H.
------------- exact H.
-------- exact H8.
Qed.
