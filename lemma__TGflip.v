Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export logic.
Definition lemma__TGflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.TG A a B b C c) -> ((euclidean__defs.TG a A B b C c) /\ (euclidean__defs.TG A a B b c C)).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (* Cut *) (exists (H0: euclidean__axioms.Point), (euclidean__axioms.BetS A a H0) /\ ((euclidean__axioms.Cong a H0 B b) /\ (euclidean__defs.Lt C c A H0))) as H0.
- exact H.
- assert (exists H1: euclidean__axioms.Point, ((euclidean__axioms.BetS A a H1) /\ ((euclidean__axioms.Cong a H1 B b) /\ (euclidean__defs.Lt C c A H1)))) as H2.
-- exact H0.
-- destruct H2 as [H1 H2].
assert (* AndElim *) ((euclidean__axioms.BetS A a H1) /\ ((euclidean__axioms.Cong a H1 B b) /\ (euclidean__defs.Lt C c A H1))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong a H1 B b) /\ (euclidean__defs.Lt C c A H1)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* Cut *) (euclidean__axioms.neq A a) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H7.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (H1) H3).
------ assert (* AndElim *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
exact H10.
----- assert (* Cut *) (euclidean__axioms.neq a A) as H8.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (a) H7).
------ assert (* Cut *) (euclidean__axioms.neq a H1) as H9.
------- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H9.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (H1) H3).
-------- assert (* AndElim *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1)) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
exact H10.
------- assert (* Cut *) (euclidean__axioms.neq B b) as H10.
-------- apply (@euclidean__axioms.axiom__nocollapse (a) (H1) (B) (b) (H9) H5).
-------- assert (* Cut *) (exists (h: euclidean__axioms.Point), (euclidean__axioms.BetS a A h) /\ (euclidean__axioms.Cong A h B b)) as H11.
--------- apply (@lemma__extension.lemma__extension (a) (A) (B) (b) (H8) H10).
--------- assert (exists h: euclidean__axioms.Point, ((euclidean__axioms.BetS a A h) /\ (euclidean__axioms.Cong A h B b))) as H12.
---------- exact H11.
---------- destruct H12 as [h H12].
assert (* AndElim *) ((euclidean__axioms.BetS a A h) /\ (euclidean__axioms.Cong A h B b)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.Cong A a a A) as H15.
------------ apply (@euclidean__axioms.cn__equalityreverse (A) a).
------------ assert (* Cut *) (euclidean__axioms.Cong B b A h) as H16.
------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (h) (b) H14).
------------- assert (* Cut *) (euclidean__axioms.Cong a H1 A h) as H17.
-------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (H1) (B) (b) (A) (h) (H5) H16).
-------------- assert (* Cut *) (euclidean__axioms.Cong A H1 a h) as H18.
--------------- apply (@euclidean__axioms.cn__sumofparts (A) (a) (H1) (a) (A) (h) (H15) (H17) (H3) H13).
--------------- assert (* Cut *) (euclidean__defs.Lt C c a h) as H19.
---------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (c) (A) (H1) (a) (h) (H6) H18).
---------------- assert (* Cut *) (euclidean__defs.TG a A B b C c) as H20.
----------------- exists h.
split.
------------------ exact H13.
------------------ split.
------------------- exact H14.
------------------- exact H19.
----------------- assert (* Cut *) (euclidean__axioms.Cong C c c C) as H21.
------------------ apply (@euclidean__axioms.cn__equalityreverse (C) c).
------------------ assert (* Cut *) (euclidean__defs.Lt c C A H1) as H22.
------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (c) (A) (H1) (c) (C) (H6) H21).
------------------- assert (* Cut *) (euclidean__defs.TG A a B b c C) as H23.
-------------------- exists H1.
split.
--------------------- exact H3.
--------------------- split.
---------------------- exact H5.
---------------------- exact H22.
-------------------- assert (* Cut *) (euclidean__defs.Lt C c a h) as H24.
--------------------- exact H19.
--------------------- split.
---------------------- exact H20.
---------------------- exact H23.
Qed.
