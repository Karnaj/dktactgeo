Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ray1.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__tworays : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Out A B C) -> ((euclidean__defs.Out B A C) -> (euclidean__axioms.BetS A C B)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as H1.
- apply (@lemma__ray1.lemma__ray1 (A) (B) (C) H).
- assert (* Cut *) ((euclidean__axioms.BetS B C A) \/ ((A = C) \/ (euclidean__axioms.BetS B A C))) as H2.
-- apply (@lemma__ray1.lemma__ray1 (B) (A) (C) H0).
-- assert (* Cut *) (euclidean__axioms.BetS A C B) as H3.
--- assert (* Cut *) ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as H3.
---- exact H1.
---- assert (* Cut *) ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as __TmpHyp.
----- exact H3.
----- assert (euclidean__axioms.BetS A C B \/ (B = C) \/ (euclidean__axioms.BetS A B C)) as H4.
------ exact __TmpHyp.
------ destruct H4 as [H4|H4].
------- exact H4.
------- assert (B = C \/ euclidean__axioms.BetS A B C) as H5.
-------- exact H4.
-------- destruct H5 as [H5|H5].
--------- assert (* Cut *) (~(~(euclidean__axioms.BetS A C B))) as H6.
---------- intro H6.
assert (* Cut *) (euclidean__axioms.neq B C) as H7.
----------- apply (@lemma__raystrict.lemma__raystrict (B) (A) (C) H0).
----------- apply (@H7 H5).
---------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A C B)).
-----------intro H7.
assert (euclidean__axioms.BetS B C A \/ (A = C) \/ (euclidean__axioms.BetS B A C)) as H8.
------------ exact H2.
------------ destruct H8 as [H8|H8].
------------- assert (* Cut *) (False) as H9.
-------------- apply (@H6 H7).
-------------- assert False.
---------------exact H9.
--------------- contradiction.
------------- assert (A = C \/ euclidean__axioms.BetS B A C) as H9.
-------------- exact H8.
-------------- destruct H9 as [H9|H9].
--------------- assert (* Cut *) (False) as H10.
---------------- apply (@H6 H7).
---------------- assert False.
-----------------exact H10.
----------------- contradiction.
--------------- assert (* Cut *) (False) as H10.
---------------- apply (@H6 H7).
---------------- assert False.
-----------------exact H10.
----------------- contradiction.

--------- assert (* Cut *) (euclidean__axioms.BetS A C B) as H6.
---------- assert (* Cut *) ((euclidean__axioms.BetS B C A) \/ ((A = C) \/ (euclidean__axioms.BetS B A C))) as H6.
----------- exact H2.
----------- assert (* Cut *) ((euclidean__axioms.BetS B C A) \/ ((A = C) \/ (euclidean__axioms.BetS B A C))) as __TmpHyp0.
------------ exact H6.
------------ assert (euclidean__axioms.BetS B C A \/ (A = C) \/ (euclidean__axioms.BetS B A C)) as H7.
------------- exact __TmpHyp0.
------------- destruct H7 as [H7|H7].
-------------- assert (* Cut *) (euclidean__axioms.BetS A C B) as H8.
--------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (A) H7).
--------------- exact H8.
-------------- assert (A = C \/ euclidean__axioms.BetS B A C) as H8.
--------------- exact H7.
--------------- destruct H8 as [H8|H8].
---------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A C B))) as H9.
----------------- intro H9.
assert (* Cut *) (euclidean__axioms.neq A C) as H10.
------------------ apply (@lemma__raystrict.lemma__raystrict (A) (B) (C) H).
------------------ apply (@H10 H8).
----------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A C B)).
------------------intro H10.
assert (* Cut *) (False) as H11.
------------------- apply (@H9 H10).
------------------- assert False.
--------------------exact H11.
-------------------- contradiction.

---------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A C B))) as H9.
----------------- intro H9.
assert (* Cut *) (euclidean__axioms.BetS A B A) as H10.
------------------ apply (@euclidean__axioms.axiom__innertransitivity (A) (B) (A) (C) (H5) H8).
------------------ assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H11.
------------------- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
------------------- apply (@H11 H10).
----------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A C B)).
------------------intro H10.
assert (* Cut *) (False) as H11.
------------------- apply (@H9 H10).
------------------- assert False.
--------------------exact H11.
-------------------- contradiction.

---------- exact H6.
--- exact H3.
Qed.
