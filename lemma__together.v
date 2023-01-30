Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export logic.
Definition lemma__together : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.TG A a B b C c) -> ((euclidean__axioms.Cong D F A a) -> ((euclidean__axioms.Cong F G B b) -> ((euclidean__axioms.BetS D F G) -> ((euclidean__axioms.Cong P Q C c) -> ((euclidean__defs.Lt P Q D G) /\ ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq B b) /\ (euclidean__axioms.neq C c)))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro F.
intro G.
intro P.
intro Q.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS A a R) /\ ((euclidean__axioms.Cong a R B b) /\ (euclidean__defs.Lt C c A R))) as H4.
- exact H.
- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS A a R) /\ ((euclidean__axioms.Cong a R B b) /\ (euclidean__defs.Lt C c A R)))) as H5.
-- exact H4.
-- destruct H5 as [R H5].
assert (* AndElim *) ((euclidean__axioms.BetS A a R) /\ ((euclidean__axioms.Cong a R B b) /\ (euclidean__defs.Lt C c A R))) as H6.
--- exact H5.
--- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Cong a R B b) /\ (euclidean__defs.Lt C c A R)) as H8.
---- exact H7.
---- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__axioms.Cong A a A a) as H10.
----- apply (@euclidean__axioms.cn__congruencereflexive (A) a).
----- assert (* Cut *) (euclidean__axioms.Cong B b a R) as H11.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (a) (R) (b) H8).
------ assert (* Cut *) (euclidean__axioms.Cong F G a R) as H12.
------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (G) (B) (b) (a) (R) (H1) H11).
------- assert (* Cut *) (euclidean__axioms.Cong D G A R) as H13.
-------- apply (@euclidean__axioms.cn__sumofparts (D) (F) (G) (A) (a) (R) (H0) (H12) (H2) H6).
-------- assert (* Cut *) (euclidean__axioms.Cong A R D G) as H14.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (D) (G) (R) H13).
--------- assert (* Cut *) (euclidean__axioms.Cong C c P Q) as H15.
---------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (P) (Q) (c) H3).
---------- assert (* Cut *) (euclidean__defs.Lt P Q A R) as H16.
----------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (c) (A) (R) (P) (Q) (H9) H15).
----------- assert (* Cut *) (euclidean__defs.Lt P Q D G) as H17.
------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (P) (Q) (A) (R) (D) (G) (H16) H14).
------------ assert (* Cut *) (euclidean__axioms.neq A a) as H18.
------------- assert (* Cut *) ((euclidean__axioms.neq a R) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R))) as H18.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (R) H6).
-------------- assert (* AndElim *) ((euclidean__axioms.neq a R) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R)) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
exact H21.
------------- assert (* Cut *) (euclidean__axioms.neq a R) as H19.
-------------- assert (* Cut *) ((euclidean__axioms.neq a R) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R))) as H19.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (R) H6).
--------------- assert (* AndElim *) ((euclidean__axioms.neq a R) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A R)) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
exact H20.
-------------- assert (* Cut *) (euclidean__axioms.neq B b) as H20.
--------------- apply (@euclidean__axioms.axiom__nocollapse (a) (R) (B) (b) (H19) H8).
--------------- assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS A S R) /\ (euclidean__axioms.Cong A S C c)) as H21.
---------------- exact H9.
---------------- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS A S R) /\ (euclidean__axioms.Cong A S C c))) as H22.
----------------- exact H21.
----------------- destruct H22 as [S H22].
assert (* AndElim *) ((euclidean__axioms.BetS A S R) /\ (euclidean__axioms.Cong A S C c)) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__axioms.neq A S) as H25.
------------------- assert (* Cut *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq A S) /\ (euclidean__axioms.neq A R))) as H25.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (S) (R) H23).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq A S) /\ (euclidean__axioms.neq A R))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A S) /\ (euclidean__axioms.neq A R)) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
exact H28.
------------------- assert (* Cut *) (euclidean__axioms.neq C c) as H26.
-------------------- apply (@euclidean__axioms.axiom__nocollapse (A) (S) (C) (c) (H25) H24).
-------------------- split.
--------------------- exact H17.
--------------------- split.
---------------------- exact H18.
---------------------- split.
----------------------- exact H20.
----------------------- exact H26.
Qed.
