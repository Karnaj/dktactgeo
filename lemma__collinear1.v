Require Export euclidean__axioms.
Require Export lemma__equalitysymmetric.
Require Export logic.
Definition lemma__collinear1 : forall A B C, (euclidean__axioms.Col A B C) -> (euclidean__axioms.Col B A C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H0 by exact H.
assert (* Cut *) (euclidean__axioms.Col B A C) as H1.
- assert ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H1 by exact H0.
assert ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as __TmpHyp by exact H1.
destruct __TmpHyp as [H2|H2].
-- assert (* Cut *) (B = A) as H3.
--- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric B A H2).
--- assert (* Cut *) (euclidean__axioms.Col B A C) as H4.
---- left.
exact H3.
---- exact H4.
-- destruct H2 as [H3|H3].
--- assert (* Cut *) (euclidean__axioms.Col B A C) as H4.
---- right.
right.
left.
exact H3.
---- exact H4.
--- destruct H3 as [H4|H4].
---- assert (* Cut *) (euclidean__axioms.Col B A C) as H5.
----- right.
left.
exact H4.
----- exact H5.
---- destruct H4 as [H5|H5].
----- assert (* Cut *) (euclidean__axioms.Col B A C) as H6.
------ right.
right.
right.
right.
left.
exact H5.
------ exact H6.
----- destruct H5 as [H6|H6].
------ assert (* Cut *) (euclidean__axioms.Col B A C) as H7.
------- right.
right.
right.
left.
exact H6.
------- exact H7.
------ assert (* Cut *) (euclidean__axioms.BetS B C A) as H7.
------- apply (@euclidean__axioms.axiom__betweennesssymmetry A C B H6).
------- assert (* Cut *) (euclidean__axioms.Col B A C) as H8.
-------- right.
right.
right.
right.
right.
exact H7.
-------- exact H8.
- exact H1.
Qed.
