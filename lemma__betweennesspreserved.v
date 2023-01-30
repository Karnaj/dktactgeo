Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__localextension.
Require Export logic.
Definition lemma__betweennesspreserved : forall A B C a b c, (euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong A C a c) -> ((euclidean__axioms.Cong B C b c) -> ((euclidean__axioms.BetS A B C) -> (euclidean__axioms.BetS a b c)))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.neq A B) as H3.
- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H3.
-- apply (@lemma__betweennotequal.lemma__betweennotequal A B C H2).
-- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
exact H6.
- assert (* Cut *) (euclidean__axioms.neq a b) as H4.
-- apply (@euclidean__axioms.axiom__nocollapse A B a b H3 H).
-- assert (* Cut *) (euclidean__axioms.neq B C) as H5.
--- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H5.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A B C H2).
---- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H6.
--- assert (* Cut *) (euclidean__axioms.neq b c) as H6.
---- apply (@euclidean__axioms.axiom__nocollapse B C b c H5 H1).
---- assert (* Cut *) (exists d, (euclidean__axioms.BetS a b d) /\ (euclidean__axioms.Cong b d b c)) as H7.
----- apply (@lemma__localextension.lemma__localextension a b c H4 H6).
----- destruct H7 as [d H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__axioms.Cong b c b d) as H11.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b b d c H10).
------ assert (* Cut *) (euclidean__axioms.Cong b c B C) as H12.
------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B C c H1).
------- assert (* Cut *) (euclidean__axioms.Cong b d B C) as H13.
-------- apply (@euclidean__axioms.cn__congruencetransitive b d B C b c H11 H12).
-------- assert (* Cut *) (euclidean__axioms.Cong B C b d) as H14.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B b d C H13).
--------- assert (* Cut *) (euclidean__axioms.Cong C C c d) as H15.
---------- apply (@euclidean__axioms.axiom__5__line A B C C a b d c H14 H0 H1 H2 H9 H).
---------- assert (* Cut *) (euclidean__axioms.Cong c d C C) as H16.
----------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric c C C d H15).
----------- assert (* Cut *) (~(euclidean__axioms.neq c d)) as H17.
------------ intro H17.
assert (* Cut *) (euclidean__axioms.neq C C) as H18.
------------- apply (@euclidean__axioms.axiom__nocollapse c d C C H17 H16).
------------- assert (* Cut *) (C = C) as H19.
-------------- assert (* Cut *) (False) as H19.
--------------- assert (* Cut *) (C = C) as H19.
---------------- apply (@logic.eq__refl Point C).
---------------- apply (@H18 H19).
--------------- assert (False) as H20 by exact H19.
apply (@logic.eq__refl Point C).
-------------- apply (@H18 H19).
------------ assert (* Cut *) (euclidean__axioms.BetS a b c) as H18.
------------- apply (@eq__ind__r euclidean__axioms.Point d (fun X => euclidean__axioms.BetS a b X)) with (x := c).
-------------- exact H9.
--------------apply (@euclidean__tactics.NNPP (c = d) H17).

------------- exact H18.
Qed.
