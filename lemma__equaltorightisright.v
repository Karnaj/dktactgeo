Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalanglessymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray5.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__equaltorightisright : forall A B C a b c, (euclidean__defs.Per A B C) -> ((euclidean__defs.CongA a b c A B C) -> (euclidean__defs.Per a b c)).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.CongA A B C a b c) as H1.
- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric a b c A B C H0).
- assert (exists E F e f, (euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)))))))) as H2 by exact H1.
destruct H2 as [E H3].
destruct H3 as [F H4].
destruct H4 as [e H5].
destruct H5 as [f H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
assert (* Cut *) (euclidean__defs.Per A B F) as H21.
-- apply (@lemma__8__3.lemma__8__3 A B C F H H9).
-- assert (* Cut *) (euclidean__defs.Per F B A) as H22.
--- apply (@lemma__8__2.lemma__8__2 A B F H21).
--- assert (* Cut *) (euclidean__defs.Per F B E) as H23.
---- apply (@lemma__8__3.lemma__8__3 F B A E H22 H7).
---- assert (* Cut *) (euclidean__defs.Per E B F) as H24.
----- apply (@lemma__8__2.lemma__8__2 F B E H23).
----- assert (* Cut *) (euclidean__axioms.neq B E) as H25.
------ apply (@lemma__raystrict.lemma__raystrict B A E H7).
------ assert (* Cut *) (euclidean__axioms.neq E B) as H26.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B E H25).
------- assert (exists W, (euclidean__axioms.BetS E B W) /\ ((euclidean__axioms.Cong E B W B) /\ ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F)))) as H27 by exact H24.
destruct H27 as [W H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
assert (* Cut *) (euclidean__axioms.neq b e) as H35.
-------- apply (@euclidean__axioms.axiom__nocollapse B E b e H25 H15).
-------- assert (* Cut *) (euclidean__axioms.neq e b) as H36.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric b e H35).
--------- assert (* Cut *) (exists w, (euclidean__axioms.BetS e b w) /\ (euclidean__axioms.Cong b w e b)) as H37.
---------- apply (@lemma__extension.lemma__extension e b e b H36 H36).
---------- destruct H37 as [w H38].
destruct H38 as [H39 H40].
assert (* Cut *) (euclidean__axioms.Cong e b E B) as H41.
----------- assert (* Cut *) ((euclidean__axioms.Cong e b E B) /\ (euclidean__axioms.Cong E B e b)) as H41.
------------ apply (@lemma__doublereverse.lemma__doublereverse B E b e H15).
------------ destruct H41 as [H42 H43].
exact H42.
----------- assert (* Cut *) (euclidean__axioms.Cong b w E B) as H42.
------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive b w e b E B H40 H41).
------------ assert (* Cut *) (euclidean__axioms.Cong E B B W) as H43.
------------- assert (* Cut *) ((euclidean__axioms.Cong B E B W) /\ ((euclidean__axioms.Cong B E W B) /\ (euclidean__axioms.Cong E B B W))) as H43.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip E B W B H31).
-------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H47.
------------- assert (* Cut *) (euclidean__axioms.Cong b w B W) as H44.
-------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive b w E B B W H42 H43).
-------------- assert (* Cut *) (euclidean__axioms.Cong b f B F) as H45.
--------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B F f H17).
--------------- assert (* Cut *) (euclidean__axioms.Cong e f E F) as H46.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric e E F f H19).
---------------- assert (* Cut *) (euclidean__axioms.Cong e w E W) as H47.
----------------- apply (@euclidean__axioms.cn__sumofparts e b w E B W H41 H44 H39 H29).
----------------- assert (* Cut *) (euclidean__axioms.Cong f w F W) as H48.
------------------ apply (@euclidean__axioms.axiom__5__line e b w f E B W F H44 H46 H45 H39 H29 H41).
------------------ assert (* Cut *) (euclidean__axioms.Cong e b B W) as H49.
------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive e b E B B W H41 H43).
------------------- assert (* Cut *) (euclidean__axioms.Cong B W b w) as H50.
-------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B b w W H44).
-------------------- assert (* Cut *) (euclidean__axioms.Cong e b b w) as H51.
--------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive e b B W b w H49 H50).
--------------------- assert (* Cut *) (euclidean__axioms.Cong e b w b) as H52.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong b e w b) /\ ((euclidean__axioms.Cong b e b w) /\ (euclidean__axioms.Cong e b w b))) as H52.
----------------------- apply (@lemma__congruenceflip.lemma__congruenceflip e b b w H51).
----------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H56.
---------------------- assert (* Cut *) (euclidean__axioms.Cong e f W F) as H53.
----------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive e f E F W F H46 H33).
----------------------- assert (* Cut *) (euclidean__axioms.Cong W F w f) as H54.
------------------------ assert (* Cut *) ((euclidean__axioms.Cong W F w f) /\ (euclidean__axioms.Cong w f W F)) as H54.
------------------------- apply (@lemma__doublereverse.lemma__doublereverse f w F W H48).
------------------------- destruct H54 as [H55 H56].
exact H55.
------------------------ assert (* Cut *) (euclidean__axioms.Cong e f w f) as H55.
------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive e f W F w f H53 H54).
------------------------- assert (* Cut *) (euclidean__axioms.neq b f) as H56.
-------------------------- apply (@lemma__raystrict.lemma__raystrict b c f H13).
-------------------------- assert (* Cut *) (euclidean__defs.Per e b f) as H57.
--------------------------- exists w.
split.
---------------------------- exact H39.
---------------------------- split.
----------------------------- exact H52.
----------------------------- split.
------------------------------ exact H55.
------------------------------ exact H56.
--------------------------- assert (* Cut *) (euclidean__defs.Out b f c) as H58.
---------------------------- apply (@lemma__ray5.lemma__ray5 b c f H13).
---------------------------- assert (* Cut *) (euclidean__defs.Per e b c) as H59.
----------------------------- apply (@lemma__8__3.lemma__8__3 e b f c H57 H58).
----------------------------- assert (* Cut *) (euclidean__defs.Per c b e) as H60.
------------------------------ apply (@lemma__8__2.lemma__8__2 e b c H59).
------------------------------ assert (* Cut *) (euclidean__defs.Out b e a) as H61.
------------------------------- apply (@lemma__ray5.lemma__ray5 b a e H11).
------------------------------- assert (* Cut *) (euclidean__defs.Per c b a) as H62.
-------------------------------- apply (@lemma__8__3.lemma__8__3 c b e a H60 H61).
-------------------------------- assert (* Cut *) (euclidean__defs.Per a b c) as H63.
--------------------------------- apply (@lemma__8__2.lemma__8__2 c b a H62).
--------------------------------- exact H63.
Qed.
