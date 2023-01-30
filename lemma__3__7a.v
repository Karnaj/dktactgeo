Require Export euclidean__axioms.
Require Export lemma__3__6a.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__extensionunique.
Require Export lemma__localextension.
Require Export logic.
Definition lemma__3__7a : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS B C D) -> (euclidean__axioms.BetS A C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A C) as H1.
- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H1.
-- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (C) H).
-- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
exact H5.
- assert (* Cut *) (euclidean__axioms.neq C D) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H2.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (C) (D) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
exact H3.
-- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E C D)) as H3.
--- apply (@lemma__localextension.lemma__localextension (A) (C) (D) (H1) H2).
--- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E C D))) as H4.
---- exact H3.
---- destruct H4 as [E H4].
assert (* AndElim *) ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E C D)) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Cong C D C E) as H7.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (C) (E) (D) H6).
------ assert (* Cut *) (euclidean__axioms.BetS B C E) as H8.
------- apply (@lemma__3__6a.lemma__3__6a (A) (B) (C) (E) (H) H5).
------- assert (* Cut *) (D = E) as H9.
-------- apply (@lemma__extensionunique.lemma__extensionunique (B) (C) (D) (E) (H0) (H8) H7).
-------- assert (* Cut *) (euclidean__axioms.BetS A C D) as H10.
--------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__axioms.BetS B C D0) -> ((euclidean__axioms.neq C D0) -> ((euclidean__axioms.Cong C E C D0) -> ((euclidean__axioms.Cong C D0 C E) -> (euclidean__axioms.BetS A C D0)))))) with (x := D).
----------intro H10.
intro H11.
intro H12.
intro H13.
exact H5.

---------- exact H9.
---------- exact H0.
---------- exact H2.
---------- exact H6.
---------- exact H7.
--------- exact H10.
Qed.
