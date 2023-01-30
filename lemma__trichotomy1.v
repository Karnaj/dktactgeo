Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__outerconnectivity.
Require Export logic.
Definition lemma__trichotomy1 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (~(euclidean__defs.Lt A B C D)) -> ((~(euclidean__defs.Lt C D A B)) -> ((euclidean__axioms.neq A B) -> ((euclidean__axioms.neq C D) -> (euclidean__axioms.Cong A B C D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.neq B A) as H3.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H1).
- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P A B)) as H4.
-- apply (@lemma__extension.lemma__extension (B) (A) (A) (B) (H3) H1).
-- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P A B))) as H5.
--- exact H4.
--- destruct H5 as [P H5].
assert (* AndElim *) ((euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P A B)) as H6.
---- exact H5.
---- destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.BetS P A B) as H8.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (P) H6).
----- assert (* Cut *) (euclidean__axioms.neq A P) as H9.
------ assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P))) as H9.
------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (P) H6).
------- assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P)) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
exact H10.
------ assert (* Cut *) (euclidean__axioms.neq P A) as H10.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (P) H9).
------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS P A E) /\ (euclidean__axioms.Cong A E C D)) as H11.
-------- apply (@lemma__extension.lemma__extension (P) (A) (C) (D) (H10) H2).
-------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS P A E) /\ (euclidean__axioms.Cong A E C D))) as H12.
--------- exact H11.
--------- destruct H12 as [E H12].
assert (* AndElim *) ((euclidean__axioms.BetS P A E) /\ (euclidean__axioms.Cong A E C D)) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* Cut *) (~(euclidean__axioms.BetS A B E)) as H15.
----------- intro H15.
assert (* Cut *) (euclidean__axioms.Cong A B A B) as H16.
------------ apply (@euclidean__axioms.cn__congruencereflexive (A) B).
------------ assert (* Cut *) (euclidean__defs.Lt A B A E) as H17.
------------- exists B.
split.
-------------- exact H15.
-------------- exact H16.
------------- assert (* Cut *) (euclidean__defs.Lt A B C D) as H18.
-------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (A) (E) (C) (D) (H17) H14).
-------------- apply (@H H18).
----------- assert (* Cut *) (~(euclidean__axioms.BetS A E B)) as H16.
------------ intro H16.
assert (* Cut *) (euclidean__defs.Lt C D A B) as H17.
------------- exists E.
split.
-------------- exact H16.
-------------- exact H14.
------------- apply (@H0 H17).
------------ assert (* Cut *) (E = B) as H17.
------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity (P) (A) (E) (B) (H13) (H8) (H16) H15).
------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H18.
-------------- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
-------------- assert (* Cut *) (euclidean__axioms.Cong A B A E) as H19.
--------------- apply (@eq__ind__r euclidean__axioms.Point B (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS P A E0) -> ((euclidean__axioms.Cong A E0 C D) -> ((~(euclidean__axioms.BetS A B E0)) -> ((~(euclidean__axioms.BetS A E0 B)) -> (euclidean__axioms.Cong A B A E0)))))) with (x := E).
----------------intro H19.
intro H20.
intro H21.
intro H22.
exact H18.

---------------- exact H17.
---------------- exact H13.
---------------- exact H14.
---------------- exact H15.
---------------- exact H16.
--------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H20.
---------------- apply (@eq__ind__r euclidean__axioms.Point B (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS P A E0) -> ((euclidean__axioms.Cong A E0 C D) -> ((~(euclidean__axioms.BetS A B E0)) -> ((~(euclidean__axioms.BetS A E0 B)) -> ((euclidean__axioms.Cong A B A E0) -> (euclidean__axioms.Cong A B C D))))))) with (x := E).
-----------------intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
exact H21.

----------------- exact H17.
----------------- exact H13.
----------------- exact H14.
----------------- exact H15.
----------------- exact H16.
----------------- exact H19.
---------------- exact H20.
Qed.
