Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthantransitive.
Require Export lemma__ray4.
Require Export lemma__trichotomy2.
Require Export logic.
Definition lemma__subtractequals : forall A B C D E, (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS A D E) -> ((euclidean__axioms.Cong B C D E) -> ((euclidean__axioms.BetS A C E) -> (euclidean__axioms.BetS A B D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (~(euclidean__axioms.BetS A D B)) as H3.
- intro H3.
assert (* Cut *) (euclidean__axioms.BetS A D C) as H4.
-- apply (@lemma__3__6b.lemma__3__6b A D B C H3 H).
-- assert (euclidean__axioms.BetS A D C) as H5 by exact H4.
assert (* Cut *) (euclidean__axioms.BetS B C E) as H6.
--- apply (@lemma__3__6a.lemma__3__6a A B C E H H2).
--- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H7.
---- apply (@euclidean__axioms.cn__congruencereflexive B C).
---- assert (* Cut *) (euclidean__defs.Lt B C B E) as H8.
----- exists C.
split.
------ exact H6.
------ exact H7.
----- assert (* Cut *) (euclidean__axioms.Cong B E E B) as H9.
------ apply (@euclidean__axioms.cn__equalityreverse B E).
------ assert (* Cut *) (euclidean__defs.Lt B C E B) as H10.
------- apply (@lemma__lessthancongruence.lemma__lessthancongruence B C B E E B H8 H9).
------- assert (* Cut *) (euclidean__axioms.BetS D C E) as H11.
-------- apply (@lemma__3__6a.lemma__3__6a A D C E H5 H2).
-------- assert (* Cut *) (euclidean__axioms.BetS D B C) as H12.
--------- apply (@lemma__3__6a.lemma__3__6a A D B C H3 H).
--------- assert (* Cut *) (euclidean__axioms.BetS D B E) as H13.
---------- apply (@lemma__3__6b.lemma__3__6b D B C E H12 H11).
---------- assert (* Cut *) (euclidean__axioms.BetS E B D) as H14.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry D B E H13).
----------- assert (* Cut *) (euclidean__axioms.Cong E B E B) as H15.
------------ apply (@euclidean__axioms.cn__congruencereflexive E B).
------------ assert (* Cut *) (euclidean__defs.Lt E B E D) as H16.
------------- exists B.
split.
-------------- exact H14.
-------------- exact H15.
------------- assert (* Cut *) (euclidean__axioms.Cong E D D E) as H17.
-------------- apply (@euclidean__axioms.cn__equalityreverse E D).
-------------- assert (* Cut *) (euclidean__defs.Lt E B D E) as H18.
--------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence E B E D D E H16 H17).
--------------- assert (* Cut *) (euclidean__defs.Lt B C D E) as H19.
---------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive B C E B D E H10 H18).
---------------- assert (* Cut *) (euclidean__axioms.Cong D E B C) as H20.
----------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D B C E H1).
----------------- assert (* Cut *) (euclidean__defs.Lt B C B C) as H21.
------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence B C D E B C H19 H20).
------------------ assert (* Cut *) (~(euclidean__defs.Lt B C B C)) as H22.
------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 B C B C H21).
------------------- apply (@H22 H21).
- assert (* Cut *) (~(~(euclidean__axioms.BetS A B D))) as H4.
-- intro H4.
assert (* Cut *) (euclidean__axioms.BetS A B E) as H5.
--- apply (@lemma__3__6b.lemma__3__6b A B C E H H2).
--- assert (* Cut *) (B = D) as H6.
---- apply (@euclidean__axioms.axiom__connectivity A B D E H5 H0 H4 H3).
---- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H7.
----- apply (@euclidean__axioms.cn__congruencereflexive A B).
----- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H8.
------ apply (@eq__ind__r euclidean__axioms.Point D (fun B0 => (euclidean__axioms.BetS A B0 C) -> ((euclidean__axioms.Cong B0 C D E) -> ((~(euclidean__axioms.BetS A D B0)) -> ((~(euclidean__axioms.BetS A B0 D)) -> ((euclidean__axioms.BetS A B0 E) -> ((euclidean__axioms.Cong A B0 A B0) -> (euclidean__axioms.Cong A B0 A D)))))))) with (x := B).
-------intro H8.
intro H9.
intro H10.
intro H11.
intro H12.
intro H13.
exact H13.

------- exact H6.
------- exact H.
------- exact H1.
------- exact H3.
------- exact H4.
------- exact H5.
------- exact H7.
------ assert (* Cut *) (euclidean__axioms.Cong A C A E) as H9.
------- apply (@euclidean__axioms.cn__sumofparts A B C A D E H8 H1 H H0).
------- assert (* Cut *) (euclidean__axioms.BetS A B E) as H10.
-------- apply (@eq__ind__r euclidean__axioms.Point D (fun B0 => (euclidean__axioms.BetS A B0 C) -> ((euclidean__axioms.Cong B0 C D E) -> ((~(euclidean__axioms.BetS A D B0)) -> ((~(euclidean__axioms.BetS A B0 D)) -> ((euclidean__axioms.BetS A B0 E) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A D) -> (euclidean__axioms.BetS A B0 E))))))))) with (x := B).
---------intro H10.
intro H11.
intro H12.
intro H13.
intro H14.
intro H15.
intro H16.
exact H14.

--------- exact H6.
--------- exact H.
--------- exact H1.
--------- exact H3.
--------- exact H4.
--------- exact H5.
--------- exact H7.
--------- exact H8.
-------- assert (* Cut *) (euclidean__axioms.neq A B) as H11.
--------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H11.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal A B E H10).
---------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
--------- assert (* Cut *) (euclidean__defs.Out A B E) as H12.
---------- apply (@lemma__ray4.lemma__ray4 A B E).
-----------right.
right.
exact H10.

----------- exact H11.
---------- assert (* Cut *) (euclidean__defs.Out A B C) as H13.
----------- apply (@lemma__ray4.lemma__ray4 A B C).
------------right.
right.
exact H.

------------ exact H11.
----------- assert (* Cut *) (C = E) as H14.
------------ apply (@lemma__layoffunique.lemma__layoffunique A B C E H13 H12 H9).
------------ assert (* Cut *) (euclidean__axioms.neq C E) as H15.
------------- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A E))) as H15.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C E H2).
-------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
------------- apply (@H15 H14).
-- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A B D)).
---intro H5.
assert (* Cut *) (False) as H6.
---- apply (@H4 H5).
---- contradiction H6.

Qed.
