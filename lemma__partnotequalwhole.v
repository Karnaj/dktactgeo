Require Export euclidean__axioms.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__partnotequalwhole : forall A B C, (euclidean__axioms.BetS A B C) -> (~(euclidean__axioms.Cong A B A C)).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.neq A B) as H0.
- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H0.
-- apply (@lemma__betweennotequal.lemma__betweennotequal A B C H).
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
exact H3.
- assert (* Cut *) (euclidean__axioms.neq B A) as H1.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H0).
-- assert (* Cut *) (exists D, euclidean__axioms.BetS B A D) as H2.
--- apply (@euclidean__axioms.postulate__Euclid2 B A H1).
--- destruct H2 as [D H3].
assert (* Cut *) (euclidean__axioms.BetS D A B) as H4.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry B A D H3).
---- assert (* Cut *) (euclidean__axioms.BetS D A C) as H5.
----- apply (@lemma__3__7b.lemma__3__7b D A B C H4 H).
----- assert (* Cut *) (euclidean__axioms.neq B C) as H6.
------ assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H6.
------- apply (@lemma__betweennotequal.lemma__betweennotequal A B C H).
------- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H7.
------ assert (* Cut *) (~(euclidean__axioms.Cong A B A C)) as H7.
------- intro H7.
assert (* Cut *) (B = C) as H8.
-------- apply (@lemma__extensionunique.lemma__extensionunique D A B C H4 H5 H7).
-------- apply (@H6 H8).
------- exact H7.
Qed.
