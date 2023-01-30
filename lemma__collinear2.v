Require Export euclidean__axioms.
Require Export lemma__equalitysymmetric.
Require Export logic.
Definition lemma__collinear2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Col A B C) -> (euclidean__axioms.Col B C A).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H0.
- exact H.
- assert (* Cut *) (euclidean__axioms.Col B C A) as H1.
-- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H1.
--- exact H0.
--- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as __TmpHyp.
---- exact H1.
---- assert (A = B \/ (A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as H2.
----- exact __TmpHyp.
----- destruct H2 as [H2|H2].
------ assert (* Cut *) (B = A) as H3.
------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (B) (A) H2).
------- assert (* Cut *) (euclidean__axioms.Col B C A) as H4.
-------- right.
left.
exact H3.
-------- exact H4.
------ assert (A = C \/ (B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) as H3.
------- exact H2.
------- destruct H3 as [H3|H3].
-------- assert (* Cut *) (C = A) as H4.
--------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (C) (A) H3).
--------- assert (* Cut *) (euclidean__axioms.Col B C A) as H5.
---------- right.
right.
left.
exact H4.
---------- exact H5.
-------- assert (B = C \/ (euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as H4.
--------- exact H3.
--------- destruct H4 as [H4|H4].
---------- assert (* Cut *) (euclidean__axioms.Col B C A) as H5.
----------- left.
exact H4.
----------- exact H5.
---------- assert (euclidean__axioms.BetS B A C \/ (euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) as H5.
----------- exact H4.
----------- destruct H5 as [H5|H5].
------------ assert (* Cut *) (euclidean__axioms.Col B C A) as H6.
------------- right.
right.
right.
right.
right.
exact H5.
------------- exact H6.
------------ assert (euclidean__axioms.BetS A B C \/ euclidean__axioms.BetS A C B) as H6.
------------- exact H5.
------------- destruct H6 as [H6|H6].
-------------- assert (* Cut *) (euclidean__axioms.BetS C B A) as H7.
--------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (C) H6).
--------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H8.
---------------- right.
right.
right.
left.
exact H7.
---------------- exact H8.
-------------- assert (* Cut *) (euclidean__axioms.BetS B C A) as H7.
--------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (C) (B) H6).
--------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H8.
---------------- right.
right.
right.
right.
left.
exact H7.
---------------- exact H8.
-- exact H1.
Qed.
