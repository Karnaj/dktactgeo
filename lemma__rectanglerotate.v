Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Definition lemma__rectanglerotate : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.RE A B C D) -> (euclidean__defs.RE B C D A).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0.
- assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H3.
----- exact H2.
----- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
split.
-------- exact H1.
-------- split.
--------- exact H3.
--------- split.
---------- exact H5.
---------- split.
----------- exact H7.
----------- exact H8.
- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H1.
-- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D)))))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D)))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
exact H8.
-- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H2.
--- exact H1.
--- destruct H2 as [M H2].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H5.
----- exact H0.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* Cut *) (euclidean__axioms.BetS C M A) as H13.
--------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (C) H3).
--------- assert (* Cut *) (euclidean__defs.CR B D C A) as H14.
---------- exists M.
split.
----------- exact H4.
----------- exact H13.
---------- assert (* Cut *) (euclidean__defs.RE B C D A) as H15.
----------- split.
------------ exact H7.
------------ split.
------------- exact H9.
------------- split.
-------------- exact H11.
-------------- split.
--------------- exact H5.
--------------- exact H14.
----------- exact H15.
Qed.
