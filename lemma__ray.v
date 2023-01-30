Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export lemma__lessthancongruence.
Require Export lemma__ray2.
Require Export logic.
Definition lemma__ray : forall A B P, (euclidean__defs.Out A B P) -> ((euclidean__axioms.neq P B) -> ((~(euclidean__axioms.BetS A P B)) -> (euclidean__axioms.BetS A B P))).
Proof.
intro A.
intro B.
intro P.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq A B) as H2.
- apply (@lemma__ray2.lemma__ray2 A B P H).
- assert (exists E, (euclidean__axioms.BetS E A P) /\ (euclidean__axioms.BetS E A B)) as H3 by exact H.
destruct H3 as [E H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.neq A P) as H7.
-- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E P))) as H7.
--- apply (@lemma__betweennotequal.lemma__betweennotequal E A P H5).
--- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H8.
-- assert (* Cut *) (exists D, (euclidean__axioms.BetS A B D) /\ (euclidean__axioms.Cong B D A P)) as H8.
--- apply (@lemma__extension.lemma__extension A B A P H2 H7).
--- destruct H8 as [D H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Cong D B B D) as H12.
---- apply (@euclidean__axioms.cn__equalityreverse D B).
---- assert (* Cut *) (euclidean__axioms.Cong D B A P) as H13.
----- apply (@lemma__congruencetransitive.lemma__congruencetransitive D B B D A P H12 H11).
----- assert (* Cut *) (euclidean__axioms.BetS D B A) as H14.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry A B D H10).
------ assert (* Cut *) (euclidean__defs.Lt A P D A) as H15.
------- exists B.
split.
-------- exact H14.
-------- exact H13.
------- assert (* Cut *) (euclidean__axioms.Cong D A A D) as H16.
-------- apply (@euclidean__axioms.cn__equalityreverse D A).
-------- assert (* Cut *) (euclidean__defs.Lt A P A D) as H17.
--------- apply (@lemma__lessthancongruence.lemma__lessthancongruence A P D A A D H15 H16).
--------- assert (exists F, (euclidean__axioms.BetS A F D) /\ (euclidean__axioms.Cong A F A P)) as H18 by exact H17.
destruct H18 as [F H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__axioms.BetS E A D) as H22.
---------- apply (@lemma__3__7b.lemma__3__7b E A B D H6 H10).
---------- assert (* Cut *) (euclidean__axioms.BetS E A F) as H23.
----------- apply (@euclidean__axioms.axiom__innertransitivity E A F D H22 H20).
----------- assert (* Cut *) (euclidean__axioms.Cong A P A F) as H24.
------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A F P H21).
------------ assert (* Cut *) (P = F) as H25.
------------- apply (@lemma__extensionunique.lemma__extensionunique E A P F H5 H23 H24).
------------- assert (* Cut *) (euclidean__axioms.BetS A P D) as H26.
-------------- apply (@eq__ind__r euclidean__axioms.Point F (fun P0 => (euclidean__defs.Out A B P0) -> ((euclidean__axioms.neq P0 B) -> ((~(euclidean__axioms.BetS A P0 B)) -> ((euclidean__axioms.BetS E A P0) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.Cong B D A P0) -> ((euclidean__axioms.Cong D B A P0) -> ((euclidean__defs.Lt A P0 D A) -> ((euclidean__defs.Lt A P0 A D) -> ((euclidean__axioms.Cong A F A P0) -> ((euclidean__axioms.Cong A P0 A F) -> (euclidean__axioms.BetS A P0 D))))))))))))) with (x := P).
---------------intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
exact H20.

--------------- exact H25.
--------------- exact H.
--------------- exact H0.
--------------- exact H1.
--------------- exact H5.
--------------- exact H7.
--------------- exact H11.
--------------- exact H13.
--------------- exact H15.
--------------- exact H17.
--------------- exact H21.
--------------- exact H24.
-------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A B P))) as H27.
--------------- intro H27.
assert (* Cut *) (B = P) as H28.
---------------- apply (@euclidean__axioms.axiom__connectivity A B P D H10 H26 H27 H1).
---------------- assert (* Cut *) (euclidean__axioms.neq B P) as H29.
----------------- apply (@eq__ind__r euclidean__axioms.Point P (fun B0 => (euclidean__defs.Out A B0 P) -> ((euclidean__axioms.neq P B0) -> ((~(euclidean__axioms.BetS A P B0)) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.BetS E A B0) -> ((euclidean__axioms.BetS A B0 D) -> ((euclidean__axioms.Cong B0 D A P) -> ((euclidean__axioms.Cong D B0 B0 D) -> ((euclidean__axioms.Cong D B0 A P) -> ((euclidean__axioms.BetS D B0 A) -> ((~(euclidean__axioms.BetS A B0 P)) -> (euclidean__axioms.neq B0 P))))))))))))) with (x := B).
------------------intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
apply (@eq__ind__r euclidean__axioms.Point F (fun P0 => (euclidean__axioms.neq A P0) -> ((~(euclidean__axioms.BetS A P0 P0)) -> ((euclidean__axioms.neq P0 P0) -> ((euclidean__defs.Out A P0 P0) -> ((euclidean__axioms.BetS E A P0) -> ((euclidean__axioms.BetS E A P0) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.BetS D P0 A) -> ((euclidean__axioms.Cong D P0 A P0) -> ((euclidean__axioms.Cong D P0 P0 D) -> ((euclidean__axioms.Cong P0 D A P0) -> ((euclidean__axioms.BetS A P0 D) -> ((euclidean__defs.Lt A P0 D A) -> ((euclidean__defs.Lt A P0 A D) -> ((euclidean__axioms.Cong A F A P0) -> ((euclidean__axioms.Cong A P0 A F) -> ((euclidean__axioms.BetS A P0 D) -> ((~(euclidean__axioms.BetS A P0 P0)) -> (euclidean__axioms.neq P0 P0)))))))))))))))))))) with (x := P).
-------------------intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
exact H42.

------------------- exact H25.
------------------- exact H32.
------------------- exact H31.
------------------- exact H30.
------------------- exact H29.
------------------- exact H5.
------------------- exact H33.
------------------- exact H7.
------------------- exact H38.
------------------- exact H37.
------------------- exact H36.
------------------- exact H35.
------------------- exact H34.
------------------- exact H15.
------------------- exact H17.
------------------- exact H21.
------------------- exact H24.
------------------- exact H26.
------------------- exact H39.

------------------ exact H28.
------------------ exact H.
------------------ exact H0.
------------------ exact H1.
------------------ exact H2.
------------------ exact H6.
------------------ exact H10.
------------------ exact H11.
------------------ exact H12.
------------------ exact H13.
------------------ exact H14.
------------------ exact H27.
----------------- apply (@H29 H28).
--------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A B P)).
----------------intro H28.
assert (* Cut *) (False) as H29.
----------------- apply (@H27 H28).
----------------- contradiction H29.

Qed.
