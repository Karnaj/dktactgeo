Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__interior5.
Require Export lemma__ray1.
Require Export logic.
Definition lemma__8__3 : forall A B C D, (euclidean__defs.Per A B C) -> ((euclidean__defs.Out B C D) -> (euclidean__defs.Per A B D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (exists E, (euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A C E C) /\ (euclidean__axioms.neq B C)))) as H1 by exact H.
destruct H1 as [E H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Cong B C B C) as H9.
- apply (@euclidean__axioms.cn__congruencereflexive B C).
- assert (* Cut *) (euclidean__axioms.Cong C D C D) as H10.
-- apply (@euclidean__axioms.cn__congruencereflexive C D).
-- assert (* Cut *) (euclidean__axioms.Cong B A B E) as H11.
--- assert (* Cut *) ((euclidean__axioms.Cong B A B E) /\ ((euclidean__axioms.Cong B A E B) /\ (euclidean__axioms.Cong A B B E))) as H11.
---- apply (@lemma__congruenceflip.lemma__congruenceflip A B E B H5).
---- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H12.
--- assert (* Cut *) (euclidean__axioms.Cong C A C E) as H12.
---- assert (* Cut *) ((euclidean__axioms.Cong C A C E) /\ ((euclidean__axioms.Cong C A E C) /\ (euclidean__axioms.Cong A C C E))) as H12.
----- apply (@lemma__congruenceflip.lemma__congruenceflip A C E C H7).
----- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H13.
---- assert (* Cut *) ((euclidean__axioms.BetS B D C) \/ ((C = D) \/ (euclidean__axioms.BetS B C D))) as H13.
----- apply (@lemma__ray1.lemma__ray1 B C D H0).
----- assert (* Cut *) (euclidean__defs.Per A B D) as H14.
------ assert ((euclidean__axioms.BetS B D C) \/ ((C = D) \/ (euclidean__axioms.BetS B C D))) as H14 by exact H13.
assert ((euclidean__axioms.BetS B D C) \/ ((C = D) \/ (euclidean__axioms.BetS B C D))) as __TmpHyp by exact H14.
destruct __TmpHyp as [H15|H15].
------- assert (* Cut *) (euclidean__axioms.Cong B D B D) as H16.
-------- apply (@euclidean__axioms.cn__congruencereflexive B D).
-------- assert (* Cut *) (euclidean__axioms.Cong D C D C) as H17.
--------- apply (@euclidean__axioms.cn__congruencereflexive D C).
--------- assert (* Cut *) (euclidean__axioms.Cong D A D E) as H18.
---------- apply (@lemma__interior5.lemma__interior5 B D C A B D C E H15 H15 H16 H17 H11 H12).
---------- assert (* Cut *) (euclidean__axioms.Cong A D E D) as H19.
----------- assert (* Cut *) ((euclidean__axioms.Cong A D E D) /\ ((euclidean__axioms.Cong A D D E) /\ (euclidean__axioms.Cong D A E D))) as H19.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip D A D E H18).
------------ destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H20.
----------- assert (* Cut *) (euclidean__axioms.neq B D) as H20.
------------ assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C))) as H20.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal B D C H15).
------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H23.
------------ assert (* Cut *) (euclidean__defs.Per A B D) as H21.
------------- exists E.
split.
-------------- exact H3.
-------------- split.
--------------- exact H5.
--------------- split.
---------------- exact H19.
---------------- exact H20.
------------- exact H21.
------- destruct H15 as [H16|H16].
-------- assert (* Cut *) (euclidean__defs.Per A B D) as H17.
--------- apply (@eq__ind__r euclidean__axioms.Point D (fun C0 => (euclidean__defs.Per A B C0) -> ((euclidean__defs.Out B C0 D) -> ((euclidean__axioms.Cong A C0 E C0) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Cong B C0 B C0) -> ((euclidean__axioms.Cong C0 D C0 D) -> ((euclidean__axioms.Cong C0 A C0 E) -> (euclidean__defs.Per A B D))))))))) with (x := C).
----------intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
exact H17.

---------- exact H16.
---------- exact H.
---------- exact H0.
---------- exact H7.
---------- exact H8.
---------- exact H9.
---------- exact H10.
---------- exact H12.
--------- exact H17.
-------- assert (* Cut *) (euclidean__axioms.Cong A D E D) as H17.
--------- apply (@euclidean__axioms.axiom__5__line B C D A B C D E H10 H11 H12 H16 H16 H9).
--------- assert (* Cut *) (euclidean__axioms.neq B D) as H18.
---------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H18.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal B C D H16).
----------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H22.
---------- assert (* Cut *) (euclidean__defs.Per A B D) as H19.
----------- exists E.
split.
------------ exact H3.
------------ split.
------------- exact H5.
------------- split.
-------------- exact H17.
-------------- exact H18.
----------- exact H19.
------ exact H14.
Qed.
