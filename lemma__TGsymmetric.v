Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export lemma__lessthancongruence.
Require Export logic.
Definition lemma__TGsymmetric : forall A B C a b c, (euclidean__defs.TG A a B b C c) -> (euclidean__defs.TG B b A a C c).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (exists H0, (euclidean__axioms.BetS A a H0) /\ ((euclidean__axioms.Cong a H0 B b) /\ (euclidean__defs.Lt C c A H0))) as H0 by exact H.
destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.neq a H1) as H7.
- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H7.
-- apply (@lemma__betweennotequal.lemma__betweennotequal A a H1 H3).
-- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H8.
- assert (* Cut *) (euclidean__axioms.neq B b) as H8.
-- apply (@euclidean__axioms.axiom__nocollapse a H1 B b H7 H5).
-- assert (* Cut *) (euclidean__axioms.neq A a) as H9.
--- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H9.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A a H1 H3).
---- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H12.
--- assert (* Cut *) (exists F, (euclidean__axioms.BetS B b F) /\ (euclidean__axioms.Cong b F A a)) as H10.
---- apply (@lemma__extension.lemma__extension B b A a H8 H9).
---- destruct H10 as [F H11].
destruct H11 as [H12 H13].
assert (* Cut *) (euclidean__axioms.Cong a A F b) as H14.
----- assert (* Cut *) ((euclidean__axioms.Cong a A F b) /\ (euclidean__axioms.Cong F b a A)) as H14.
------ apply (@lemma__doublereverse.lemma__doublereverse b F A a H13).
------ destruct H14 as [H15 H16].
exact H15.
----- assert (* Cut *) (euclidean__axioms.Cong A a F b) as H15.
------ assert (* Cut *) ((euclidean__axioms.Cong A a b F) /\ ((euclidean__axioms.Cong A a F b) /\ (euclidean__axioms.Cong a A b F))) as H15.
------- apply (@lemma__congruenceflip.lemma__congruenceflip a A F b H14).
------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H18.
------ assert (* Cut *) (euclidean__axioms.Cong a H1 b B) as H16.
------- assert (* Cut *) ((euclidean__axioms.Cong H1 a b B) /\ ((euclidean__axioms.Cong H1 a B b) /\ (euclidean__axioms.Cong a H1 b B))) as H16.
-------- apply (@lemma__congruenceflip.lemma__congruenceflip a H1 B b H5).
-------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
------- assert (* Cut *) (euclidean__axioms.BetS F b B) as H17.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry B b F H12).
-------- assert (* Cut *) (euclidean__axioms.Cong A H1 F B) as H18.
--------- apply (@euclidean__axioms.cn__sumofparts A a H1 F b B H15 H16 H3 H17).
--------- assert (* Cut *) (euclidean__axioms.Cong A H1 B F) as H19.
---------- assert (* Cut *) ((euclidean__axioms.Cong H1 A B F) /\ ((euclidean__axioms.Cong H1 A F B) /\ (euclidean__axioms.Cong A H1 B F))) as H19.
----------- apply (@lemma__congruenceflip.lemma__congruenceflip A H1 F B H18).
----------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H23.
---------- assert (* Cut *) (euclidean__defs.Lt C c B F) as H20.
----------- apply (@lemma__lessthancongruence.lemma__lessthancongruence C c A H1 B F H6 H19).
----------- assert (* Cut *) (euclidean__defs.TG B b A a C c) as H21.
------------ exists F.
split.
------------- exact H12.
------------- split.
-------------- exact H13.
-------------- exact H20.
------------ exact H21.
Qed.
