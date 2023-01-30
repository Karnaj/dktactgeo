Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__betweennotequal.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__ondiameter : forall D F K M N P Q, (euclidean__axioms.CI K F P Q) -> ((euclidean__axioms.Cong F D P Q) -> ((euclidean__axioms.Cong F M P Q) -> ((euclidean__axioms.BetS D F M) -> ((euclidean__axioms.BetS D N M) -> (euclidean__axioms.InCirc N K))))).
Proof.
intro D.
intro F.
intro K.
intro M.
intro N.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__axioms.neq D F) as H4.
- assert (* Cut *) ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D M))) as H4.
-- apply (@lemma__betweennotequal.lemma__betweennotequal D F M H2).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H7.
- assert (* Cut *) (euclidean__axioms.neq F D) as H5.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D F H4).
-- assert (* Cut *) (~(~((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))))) as H6.
--- intro H6.
assert (* Cut *) (~(euclidean__axioms.BetS D F N)) as H7.
---- intro H7.
assert (* Cut *) (euclidean__axioms.BetS F N M) as H8.
----- apply (@lemma__3__6a.lemma__3__6a D F N M H7 H3).
----- apply (@H6).
------right.
left.
exact H8.

---- assert (* Cut *) (F = N) as H8.
----- apply (@euclidean__axioms.axiom__connectivity D F N M H2 H3 H7).
------intro H8.
apply (@H6).
-------left.
exact H8.


----- apply (@H6).
------right.
right.
exact H8.

--- assert (* Cut *) (euclidean__axioms.Cong F N F N) as H7.
---- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H7.
----- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
----- apply (@euclidean__axioms.cn__congruencereflexive F N).
---- assert (* Cut *) (euclidean__axioms.InCirc N K) as H8.
----- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H8.
------ apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N)))).
-------intro H8.
assert (* Cut *) (False) as H9.
-------- apply (@H6 H8).
-------- assert (* Cut *) ((euclidean__axioms.BetS D N F) -> False) as H10.
--------- intro H10.
apply (@H8).
----------left.
exact H10.

--------- assert (* Cut *) (((euclidean__axioms.BetS F N M) \/ (F = N)) -> False) as H11.
---------- intro H11.
apply (@H8).
-----------right.
exact H11.

---------- assert (* Cut *) ((euclidean__axioms.BetS F N M) -> False) as H12.
----------- intro H12.
apply (@H11).
------------left.
exact H12.

----------- assert (* Cut *) ((F = N) -> False) as H13.
------------ intro H13.
apply (@H11).
-------------right.
exact H13.

------------ contradiction H9.

------ assert ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H9 by exact H8.
assert ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as __TmpHyp by exact H9.
destruct __TmpHyp as [H10|H10].
------- assert (* Cut *) (euclidean__axioms.BetS F N D) as H11.
-------- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H11.
--------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
--------- apply (@euclidean__axioms.axiom__betweennesssymmetry D N F H10).
-------- assert (* Cut *) (euclidean__axioms.InCirc N K) as H12.
--------- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H12.
---------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
---------- exists D.
exists N.
exists F.
exists P.
exists Q.
split.
----------- exact H.
----------- right.
split.
------------ exact H11.
------------ split.
------------- exact H0.
------------- exact H7.
--------- exact H12.
------- destruct H10 as [H11|H11].
-------- assert (* Cut *) (euclidean__axioms.InCirc N K) as H12.
--------- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H12.
---------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
---------- exists M.
exists N.
exists F.
exists P.
exists Q.
split.
----------- exact H.
----------- right.
split.
------------ exact H11.
------------ split.
------------- exact H1.
------------- exact H7.
--------- exact H12.
-------- assert (* Cut *) (N = F) as H12.
--------- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H12.
---------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
---------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric N F H11).
--------- assert (* Cut *) (euclidean__axioms.InCirc N K) as H13.
---------- assert (* Cut *) ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) as H13.
----------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS D N F) \/ ((euclidean__axioms.BetS F N M) \/ (F = N))) H6).
----------- exists M.
exists M.
exists F.
exists P.
exists Q.
split.
------------ exact H.
------------ left.
exact H12.
---------- exact H13.
----- exact H8.
Qed.
