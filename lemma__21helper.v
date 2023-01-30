Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7a.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__differenceofparts.
Require Export lemma__extension.
Require Export lemma__lessthanadditive.
Require Export lemma__lessthanbetween.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export logic.
Definition lemma__21helper : forall A B C E, (euclidean__defs.TG B A A E B E) -> ((euclidean__axioms.BetS A E C) -> (euclidean__defs.TT B A A C B E E C)).
Proof.
intro A.
intro B.
intro C.
intro E.
intro H.
intro H0.
assert (exists H1, (euclidean__axioms.BetS B A H1) /\ ((euclidean__axioms.Cong A H1 A E) /\ (euclidean__defs.Lt B E B H1))) as H1 by exact H.
destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.neq B A) as H8.
- assert (* Cut *) ((euclidean__axioms.neq A H2) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B H2))) as H8.
-- apply (@lemma__betweennotequal.lemma__betweennotequal B A H2 H4).
-- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H11.
- assert (* Cut *) (~(B = E)) as H9.
-- intro H9.
assert (* Cut *) (euclidean__defs.Lt B B B H2) as H10.
--- apply (@eq__ind__r euclidean__axioms.Point E (fun B0 => (euclidean__defs.TG B0 A A E B0 E) -> ((euclidean__axioms.BetS B0 A H2) -> ((euclidean__defs.Lt B0 E B0 H2) -> ((euclidean__axioms.neq B0 A) -> (euclidean__defs.Lt B0 B0 B0 H2)))))) with (x := B).
----intro H10.
intro H11.
intro H12.
intro H13.
exact H12.

---- exact H9.
---- exact H.
---- exact H4.
---- exact H7.
---- exact H8.
--- assert (exists K, (euclidean__axioms.BetS B K H2) /\ (euclidean__axioms.Cong B K B B)) as H11 by exact H10.
destruct H11 as [K H12].
destruct H12 as [H13 H14].
assert (* Cut *) (~(euclidean__axioms.neq B K)) as H15.
---- intro H15.
assert (* Cut *) (euclidean__axioms.neq B B) as H16.
----- apply (@euclidean__axioms.axiom__nocollapse B K B B H15 H14).
----- assert (* Cut *) (B = B) as H17.
------ assert (* Cut *) (False) as H17.
------- assert (* Cut *) (B = B) as H17.
-------- apply (@logic.eq__refl Point B).
-------- apply (@H16 H17).
------- assert (False) as H18 by exact H17.
apply (@logic.eq__refl Point B).
------ apply (@H16 H17).
---- assert (* Cut *) (euclidean__axioms.BetS B B H2) as H16.
----- apply (@eq__ind__r euclidean__axioms.Point K (fun X => euclidean__axioms.BetS B X H2)) with (x := B).
------ exact H13.
------apply (@euclidean__tactics.NNPP (B = K) H15).

----- assert (* Cut *) (euclidean__axioms.neq B B) as H17.
------ assert (* Cut *) ((euclidean__axioms.neq B H2) /\ ((euclidean__axioms.neq B B) /\ (euclidean__axioms.neq B H2))) as H17.
------- apply (@lemma__betweennotequal.lemma__betweennotequal B B H2 H16).
------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H20.
------ assert (* Cut *) (B = B) as H18.
------- assert (* Cut *) (False) as H18.
-------- assert (* Cut *) (B = B) as H18.
--------- apply (@logic.eq__refl Point B).
--------- apply (@H17 H18).
-------- assert (False) as H19 by exact H18.
apply (@logic.eq__refl Point B).
------- apply (@H17 H18).
-- assert (* Cut *) (euclidean__axioms.neq A C) as H10.
--- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H10.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A E C H0).
---- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H14.
--- assert (* Cut *) (exists F, (euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F A C)) as H11.
---- apply (@lemma__extension.lemma__extension B A A C H8 H10).
---- destruct H11 as [F H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__axioms.neq E C) as H15.
----- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C))) as H15.
------ apply (@lemma__betweennotequal.lemma__betweennotequal A E C H0).
------ destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
----- assert (* Cut *) (exists G, (euclidean__axioms.BetS B E G) /\ (euclidean__axioms.Cong E G E C)) as H16.
------ apply (@lemma__extension.lemma__extension B E E C H9 H15).
------ destruct H16 as [G H17].
destruct H17 as [H18 H19].
assert (* Cut *) (euclidean__axioms.Cong A C A F) as H20.
------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A F C H14).
------- assert (* Cut *) (euclidean__axioms.Cong A E A H2) as H21.
-------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A H2 E H6).
-------- assert (* Cut *) (euclidean__axioms.Cong A E A E) as H22.
--------- apply (@euclidean__axioms.cn__congruencereflexive A E).
--------- assert (* Cut *) (euclidean__defs.Lt A E A C) as H23.
---------- exists E.
split.
----------- exact H0.
----------- exact H22.
---------- assert (* Cut *) (euclidean__defs.Lt A E A F) as H24.
----------- apply (@lemma__lessthancongruence.lemma__lessthancongruence A E A C A F H23 H20).
----------- assert (* Cut *) (euclidean__defs.Lt A H2 A F) as H25.
------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 A E A F A H2 H24 H21).
------------ assert (* Cut *) (euclidean__defs.Out A H2 F) as H26.
------------- exists B.
split.
-------------- exact H13.
-------------- exact H4.
------------- assert (* Cut *) (euclidean__axioms.BetS A H2 F) as H27.
-------------- apply (@lemma__lessthanbetween.lemma__lessthanbetween A H2 F H25 H26).
-------------- assert (* Cut *) (euclidean__axioms.Cong E C H2 F) as H28.
--------------- apply (@lemma__differenceofparts.lemma__differenceofparts A E C A H2 F H21 H20 H0 H27).
--------------- assert (* Cut *) (euclidean__axioms.Cong E G H2 F) as H29.
---------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive E G E C H2 F H19 H28).
---------------- assert (* Cut *) (euclidean__axioms.BetS B H2 F) as H30.
----------------- apply (@lemma__3__7a.lemma__3__7a B A H2 F H4 H27).
----------------- assert (* Cut *) (euclidean__defs.Lt B G B F) as H31.
------------------ apply (@lemma__lessthanadditive.lemma__lessthanadditive B E B H2 G F H7 H18 H30 H29).
------------------ assert (* Cut *) (euclidean__defs.TG B A A C B G) as H32.
------------------- exists F.
split.
-------------------- exact H13.
-------------------- split.
--------------------- exact H14.
--------------------- exact H31.
------------------- assert (* Cut *) (euclidean__defs.TT B A A C B E E C) as H33.
-------------------- exists G.
split.
--------------------- exact H18.
--------------------- split.
---------------------- exact H19.
---------------------- exact H32.
-------------------- exact H33.
Qed.
