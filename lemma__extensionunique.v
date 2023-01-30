Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__congruencesymmetric.
Require Export logic.
Definition lemma__extensionunique : forall A B E F, (euclidean__axioms.BetS A B E) -> ((euclidean__axioms.BetS A B F) -> ((euclidean__axioms.Cong B E B F) -> (E = F))).
Proof.
intro A.
intro B.
intro E.
intro F.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.Cong B E B E) as H2.
- apply (@euclidean__axioms.cn__congruencereflexive B E).
- assert (* Cut *) (euclidean__axioms.Cong B F B E) as H3.
-- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B B E F H1).
-- assert (* Cut *) (euclidean__axioms.Cong A E A E) as H4.
--- apply (@euclidean__axioms.cn__congruencereflexive A E).
--- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H5.
---- apply (@euclidean__axioms.cn__congruencereflexive A B).
---- assert (euclidean__axioms.Cong B E B F) as H6 by exact H1.
assert (* Cut *) (euclidean__axioms.Cong E E E F) as H7.
----- apply (@euclidean__axioms.axiom__5__line A B E E A B F E H6 H4 H2 H H0 H5).
----- assert (* Cut *) (euclidean__axioms.Cong E F E E) as H8.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E E E F H7).
------ assert (* Cut *) (~(euclidean__axioms.neq E F)) as H9.
------- intro H9.
assert (* Cut *) (euclidean__axioms.neq E E) as H10.
-------- apply (@euclidean__axioms.axiom__nocollapse E F E E H9 H8).
-------- assert (* Cut *) (E = E) as H11.
--------- assert (* Cut *) (False) as H11.
---------- assert (* Cut *) (E = E) as H11.
----------- apply (@logic.eq__refl Point E).
----------- apply (@H10 H11).
---------- assert (False) as H12 by exact H11.
apply (@logic.eq__refl Point E).
--------- apply (@H10 H11).
------- apply (@euclidean__tactics.NNPP (E = F)).
--------intro H10.
assert (* Cut *) (False) as H11.
--------- apply (@H9 H10).
--------- contradiction H11.

Qed.
