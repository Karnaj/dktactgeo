Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray.
Require Export logic.
Definition lemma__ray1 : forall A B P, (euclidean__defs.Out A B P) -> ((euclidean__axioms.BetS A P B) \/ ((B = P) \/ (euclidean__axioms.BetS A B P))).
Proof.
intro A.
intro B.
intro P.
intro H.
assert (* Cut *) (~(~((euclidean__axioms.BetS A P B) \/ ((B = P) \/ (euclidean__axioms.BetS A B P))))) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.neq P B) as H1.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B P).
---assert (* Cut *) ((euclidean__axioms.BetS A P B) -> False) as H1.
---- intro H1.
apply (@H0).
-----left.
exact H1.

---- assert (* Cut *) (((B = P) \/ (euclidean__axioms.BetS A B P)) -> False) as H2.
----- intro H2.
apply (@H0).
------right.
exact H2.

----- assert (* Cut *) ((B = P) -> False) as H3.
------ intro H3.
apply (@H2).
-------left.
exact H3.

------ assert (* Cut *) ((euclidean__axioms.BetS A B P) -> False) as H4.
------- intro H4.
apply (@H2).
--------right.
exact H4.

------- exact H3.

-- assert (* Cut *) (euclidean__axioms.BetS A B P) as H2.
--- apply (@lemma__ray.lemma__ray A B P H H1).
----intro H2.
apply (@H0).
-----left.
exact H2.


--- apply (@H0).
----right.
right.
exact H2.

- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS A P B) \/ ((B = P) \/ (euclidean__axioms.BetS A B P)))).
--intro H1.
assert (* Cut *) (False) as H2.
--- apply (@H0 H1).
--- assert (* Cut *) ((euclidean__axioms.BetS A P B) -> False) as H3.
---- intro H3.
apply (@H1).
-----left.
exact H3.

---- assert (* Cut *) (((B = P) \/ (euclidean__axioms.BetS A B P)) -> False) as H4.
----- intro H4.
apply (@H1).
------right.
exact H4.

----- assert (* Cut *) ((B = P) -> False) as H5.
------ intro H5.
apply (@H4).
-------left.
exact H5.

------ assert (* Cut *) ((euclidean__axioms.BetS A B P) -> False) as H6.
------- intro H6.
apply (@H4).
--------right.
exact H6.

------- contradiction H2.

Qed.
