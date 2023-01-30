Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extensionunique.
Require Export logic.
Definition lemma__rightreverse : forall A B C D, (euclidean__defs.Per A B C) -> ((euclidean__axioms.BetS A B D) -> ((euclidean__axioms.Cong A B B D) -> (euclidean__axioms.Cong A C D C))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (exists E, (euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A C E C) /\ (euclidean__axioms.neq B C)))) as H2 by exact H.
destruct H2 as [E H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.Cong B D A B) as H10.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B A B D H1).
- assert (* Cut *) (euclidean__axioms.Cong B D E B) as H11.
-- apply (@lemma__congruencetransitive.lemma__congruencetransitive B D A B E B H10 H6).
-- assert (* Cut *) (euclidean__axioms.Cong B D B E) as H12.
--- assert (* Cut *) ((euclidean__axioms.Cong D B B E) /\ ((euclidean__axioms.Cong D B E B) /\ (euclidean__axioms.Cong B D B E))) as H12.
---- apply (@lemma__congruenceflip.lemma__congruenceflip B D E B H11).
---- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H16.
--- assert (* Cut *) (D = E) as H13.
---- apply (@lemma__extensionunique.lemma__extensionunique A B D E H0 H4 H12).
---- assert (* Cut *) (euclidean__axioms.Cong A C D C) as H14.
----- apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__axioms.BetS A B D0) -> ((euclidean__axioms.Cong A B B D0) -> ((euclidean__axioms.Cong B D0 A B) -> ((euclidean__axioms.Cong B D0 E B) -> ((euclidean__axioms.Cong B D0 B E) -> (euclidean__axioms.Cong A C D0 C))))))) with (x := D).
------intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
exact H8.

------ exact H13.
------ exact H0.
------ exact H1.
------ exact H10.
------ exact H11.
------ exact H12.
----- exact H14.
Qed.
