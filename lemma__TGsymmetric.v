Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export lemma__lessthancongruence.
Require Export logic.
Definition lemma__TGsymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.TG A a B b C c) -> (euclidean__defs.TG B b A a C c).
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
assert (* Cut *) (euclidean__axioms.neq a H1) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H7.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (H1) H3).
------ assert (* AndElim *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
exact H8.
----- assert (* Cut *) (euclidean__axioms.neq B b) as H8.
------ apply (@euclidean__axioms.axiom__nocollapse (a) (H1) (B) (b) (H7) H5).
------ assert (* Cut *) (euclidean__axioms.neq A a) as H9.
------- assert (* Cut *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H9.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (H1) H3).
-------- assert (* AndElim *) ((euclidean__axioms.neq a H1) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A H1)) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
exact H12.
------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B b F) /\ (euclidean__axioms.Cong b F A a)) as H10.
-------- apply (@lemma__extension.lemma__extension (B) (b) (A) (a) (H8) H9).
-------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B b F) /\ (euclidean__axioms.Cong b F A a))) as H11.
--------- exact H10.
--------- destruct H11 as [F H11].
assert (* AndElim *) ((euclidean__axioms.BetS B b F) /\ (euclidean__axioms.Cong b F A a)) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* Cut *) (euclidean__axioms.Cong a A F b) as H14.
----------- assert (* Cut *) ((euclidean__axioms.Cong a A F b) /\ (euclidean__axioms.Cong F b a A)) as H14.
------------ apply (@lemma__doublereverse.lemma__doublereverse (b) (F) (A) (a) H13).
------------ assert (* AndElim *) ((euclidean__axioms.Cong a A F b) /\ (euclidean__axioms.Cong F b a A)) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
exact H15.
----------- assert (* Cut *) (euclidean__axioms.Cong A a F b) as H15.
------------ assert (* Cut *) ((euclidean__axioms.Cong A a b F) /\ ((euclidean__axioms.Cong A a F b) /\ (euclidean__axioms.Cong a A b F))) as H15.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip (a) (A) (F) (b) H14).
------------- assert (* AndElim *) ((euclidean__axioms.Cong A a b F) /\ ((euclidean__axioms.Cong A a F b) /\ (euclidean__axioms.Cong a A b F))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A a F b) /\ (euclidean__axioms.Cong a A b F)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H18.
------------ assert (* Cut *) (euclidean__axioms.Cong a H1 b B) as H16.
------------- assert (* Cut *) ((euclidean__axioms.Cong H1 a b B) /\ ((euclidean__axioms.Cong H1 a B b) /\ (euclidean__axioms.Cong a H1 b B))) as H16.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip (a) (H1) (B) (b) H5).
-------------- assert (* AndElim *) ((euclidean__axioms.Cong H1 a b B) /\ ((euclidean__axioms.Cong H1 a B b) /\ (euclidean__axioms.Cong a H1 b B))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong H1 a B b) /\ (euclidean__axioms.Cong a H1 b B)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H20.
------------- assert (* Cut *) (euclidean__axioms.BetS F b B) as H17.
-------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (b) (F) H12).
-------------- assert (* Cut *) (euclidean__axioms.Cong A H1 F B) as H18.
--------------- apply (@euclidean__axioms.cn__sumofparts (A) (a) (H1) (F) (b) (B) (H15) (H16) (H3) H17).
--------------- assert (* Cut *) (euclidean__axioms.Cong A H1 B F) as H19.
---------------- assert (* Cut *) ((euclidean__axioms.Cong H1 A B F) /\ ((euclidean__axioms.Cong H1 A F B) /\ (euclidean__axioms.Cong A H1 B F))) as H19.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (H1) (F) (B) H18).
----------------- assert (* AndElim *) ((euclidean__axioms.Cong H1 A B F) /\ ((euclidean__axioms.Cong H1 A F B) /\ (euclidean__axioms.Cong A H1 B F))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong H1 A F B) /\ (euclidean__axioms.Cong A H1 B F)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
exact H23.
---------------- assert (* Cut *) (euclidean__defs.Lt C c B F) as H20.
----------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (c) (A) (H1) (B) (F) (H6) H19).
----------------- assert (* Cut *) (euclidean__defs.TG B b A a C c) as H21.
------------------ exists F.
split.
------------------- exact H12.
------------------- split.
-------------------- exact H13.
-------------------- exact H20.
------------------ exact H21.
Qed.
