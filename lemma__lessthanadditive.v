Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__3__7a.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__outerconnectivity.
Require Export lemma__ray4.
Require Export lemma__trichotomy2.
Require Export logic.
Definition lemma__lessthanadditive : forall A B C D E F, (euclidean__defs.Lt A B C D) -> ((euclidean__axioms.BetS A B E) -> ((euclidean__axioms.BetS C D F) -> ((euclidean__axioms.Cong B E D F) -> (euclidean__defs.Lt A E C F)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
assert (exists b, (euclidean__axioms.BetS C b D) /\ (euclidean__axioms.Cong C b A B)) as H3 by exact H.
destruct H3 as [b H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Cong A B C b) as H7.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A C b B H6).
- assert (* Cut *) (euclidean__axioms.neq C b) as H8.
-- assert (* Cut *) ((euclidean__axioms.neq b D) /\ ((euclidean__axioms.neq C b) /\ (euclidean__axioms.neq C D))) as H8.
--- apply (@lemma__betweennotequal.lemma__betweennotequal C b D H5).
--- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H11.
-- assert (* Cut *) (euclidean__axioms.neq b C) as H9.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C b H8).
--- assert (* Cut *) (euclidean__axioms.neq B E) as H10.
---- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H10.
----- apply (@lemma__betweennotequal.lemma__betweennotequal A B E H0).
----- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H11.
---- assert (* Cut *) (exists e, (euclidean__axioms.BetS C b e) /\ (euclidean__axioms.Cong b e B E)) as H11.
----- apply (@lemma__extension.lemma__extension C b B E H8 H10).
----- destruct H11 as [e H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__axioms.Cong B E b e) as H15.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B b e E H14).
------ assert (* Cut *) (euclidean__axioms.Cong A E C e) as H16.
------- apply (@euclidean__axioms.cn__sumofparts A B E C b e H7 H15 H0 H13).
------- assert (* Cut *) (euclidean__axioms.Cong e D e D) as H17.
-------- apply (@euclidean__axioms.cn__congruencereflexive e D).
-------- assert (* Cut *) (euclidean__axioms.BetS e b C) as H18.
--------- apply (@euclidean__axioms.axiom__betweennesssymmetry C b e H13).
--------- assert (* Cut *) (euclidean__axioms.BetS C b F) as H19.
---------- apply (@lemma__3__6b.lemma__3__6b C b D F H5 H1).
---------- assert (* Cut *) (~(euclidean__axioms.BetS b F e)) as H20.
----------- intro H20.
assert (* Cut *) (euclidean__axioms.Cong b F b F) as H21.
------------ apply (@euclidean__axioms.cn__congruencereflexive b F).
------------ assert (* Cut *) (euclidean__defs.Lt b F b e) as H22.
------------- exists F.
split.
-------------- exact H20.
-------------- exact H21.
------------- assert (* Cut *) (euclidean__axioms.Cong F D F D) as H23.
-------------- apply (@euclidean__axioms.cn__congruencereflexive F D).
-------------- assert (* Cut *) (euclidean__axioms.BetS b D F) as H24.
--------------- apply (@lemma__3__6a.lemma__3__6a C b D F H5 H1).
--------------- assert (* Cut *) (euclidean__axioms.BetS F D b) as H25.
---------------- apply (@euclidean__axioms.axiom__betweennesssymmetry b D F H24).
---------------- assert (* Cut *) (euclidean__defs.Lt F D F b) as H26.
----------------- exists D.
split.
------------------ exact H25.
------------------ exact H23.
----------------- assert (* Cut *) (euclidean__axioms.Cong F b b F) as H27.
------------------ apply (@euclidean__axioms.cn__equalityreverse F b).
------------------ assert (* Cut *) (euclidean__defs.Lt F D b F) as H28.
------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence F D F b b F H26 H27).
------------------- assert (* Cut *) (euclidean__axioms.Cong F D D F) as H29.
-------------------- apply (@euclidean__axioms.cn__equalityreverse F D).
-------------------- assert (* Cut *) (euclidean__defs.Lt D F b F) as H30.
--------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 F D b F D F H28 H29).
--------------------- assert (* Cut *) (euclidean__axioms.Cong b e D F) as H31.
---------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive b e B E D F H14 H2).
---------------------- assert (* Cut *) (euclidean__axioms.Cong D F b e) as H32.
----------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D b e F H31).
----------------------- assert (* Cut *) (euclidean__defs.Lt b e b F) as H33.
------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 D F b F b e H30 H32).
------------------------ assert (exists q, (euclidean__axioms.BetS b q F) /\ (euclidean__axioms.Cong b q b e)) as H34 by exact H33.
destruct H34 as [q H35].
destruct H35 as [H36 H37].
assert (* Cut *) (euclidean__axioms.neq b q) as H38.
------------------------- assert (* Cut *) ((euclidean__axioms.neq q F) /\ ((euclidean__axioms.neq b q) /\ (euclidean__axioms.neq b F))) as H38.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal b q F H36).
-------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
------------------------- assert (* Cut *) (euclidean__axioms.neq b F) as H39.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq q F) /\ ((euclidean__axioms.neq b q) /\ (euclidean__axioms.neq b F))) as H39.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal b q F H36).
--------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H43.
-------------------------- assert (* Cut *) (euclidean__defs.Out b F q) as H40.
--------------------------- apply (@lemma__ray4.lemma__ray4 b F q).
----------------------------left.
exact H36.

---------------------------- exact H39.
--------------------------- assert (* Cut *) (euclidean__defs.Out b F e) as H41.
---------------------------- apply (@lemma__ray4.lemma__ray4 b F e).
-----------------------------right.
right.
exact H20.

----------------------------- exact H39.
---------------------------- assert (* Cut *) (q = e) as H42.
----------------------------- apply (@lemma__layoffunique.lemma__layoffunique b F q e H40 H41 H37).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS b e F) as H43.
------------------------------ apply (@eq__ind__r euclidean__axioms.Point e (fun q0 => (euclidean__axioms.BetS b q0 F) -> ((euclidean__axioms.Cong b q0 b e) -> ((euclidean__axioms.neq b q0) -> ((euclidean__defs.Out b F q0) -> (euclidean__axioms.BetS b e F)))))) with (x := q).
-------------------------------intro H43.
intro H44.
intro H45.
intro H46.
exact H43.

------------------------------- exact H42.
------------------------------- exact H36.
------------------------------- exact H37.
------------------------------- exact H38.
------------------------------- exact H40.
------------------------------ assert (* Cut *) (euclidean__axioms.BetS F e F) as H44.
------------------------------- apply (@lemma__3__6a.lemma__3__6a b F e F H20 H43).
------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS F e F)) as H45.
-------------------------------- apply (@euclidean__axioms.axiom__betweennessidentity F e).
-------------------------------- apply (@H45 H44).
----------- assert (* Cut *) (~(F = e)) as H21.
------------ intro H21.
assert (* Cut *) (euclidean__axioms.Cong b F B E) as H22.
------------- apply (@eq__ind__r euclidean__axioms.Point e (fun F0 => (euclidean__axioms.BetS C D F0) -> ((euclidean__axioms.Cong B E D F0) -> ((euclidean__axioms.BetS C b F0) -> ((~(euclidean__axioms.BetS b F0 e)) -> (euclidean__axioms.Cong b F0 B E)))))) with (x := F).
--------------intro H22.
intro H23.
intro H24.
intro H25.
exact H14.

-------------- exact H21.
-------------- exact H1.
-------------- exact H2.
-------------- exact H19.
-------------- exact H20.
------------- assert (* Cut *) (euclidean__axioms.BetS b D F) as H23.
-------------- apply (@lemma__3__6a.lemma__3__6a C b D F H5 H1).
-------------- assert (* Cut *) (euclidean__axioms.BetS F D b) as H24.
--------------- apply (@euclidean__axioms.axiom__betweennesssymmetry b D F H23).
--------------- assert (* Cut *) (euclidean__axioms.Cong F D F D) as H25.
---------------- apply (@eq__ind__r euclidean__axioms.Point e (fun F0 => (euclidean__axioms.BetS C D F0) -> ((euclidean__axioms.Cong B E D F0) -> ((euclidean__axioms.BetS C b F0) -> ((~(euclidean__axioms.BetS b F0 e)) -> ((euclidean__axioms.Cong b F0 B E) -> ((euclidean__axioms.BetS b D F0) -> ((euclidean__axioms.BetS F0 D b) -> (euclidean__axioms.Cong F0 D F0 D))))))))) with (x := F).
-----------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
exact H17.

----------------- exact H21.
----------------- exact H1.
----------------- exact H2.
----------------- exact H19.
----------------- exact H20.
----------------- exact H22.
----------------- exact H23.
----------------- exact H24.
---------------- assert (* Cut *) (euclidean__defs.Lt F D F b) as H26.
----------------- exists D.
split.
------------------ exact H24.
------------------ exact H25.
----------------- assert (* Cut *) (euclidean__axioms.Cong F b b F) as H27.
------------------ apply (@euclidean__axioms.cn__equalityreverse F b).
------------------ assert (* Cut *) (euclidean__defs.Lt F D b F) as H28.
------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence F D F b b F H26 H27).
------------------- assert (* Cut *) (euclidean__axioms.Cong D F B E) as H29.
-------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D B E F H2).
-------------------- assert (* Cut *) (euclidean__axioms.Cong F D B E) as H30.
--------------------- assert (* Cut *) ((euclidean__axioms.Cong F D E B) /\ ((euclidean__axioms.Cong F D B E) /\ (euclidean__axioms.Cong D F E B))) as H30.
---------------------- apply (@lemma__congruenceflip.lemma__congruenceflip D F B E H29).
---------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H33.
--------------------- assert (* Cut *) (euclidean__defs.Lt B E b F) as H31.
---------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 F D b F B E H28 H30).
---------------------- assert (* Cut *) (euclidean__axioms.Cong b F b e) as H32.
----------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive b F B E b e H22 H15).
----------------------- assert (* Cut *) (euclidean__defs.Lt B E b e) as H33.
------------------------ apply (@eq__ind__r euclidean__axioms.Point e (fun F0 => (euclidean__axioms.BetS C D F0) -> ((euclidean__axioms.Cong B E D F0) -> ((euclidean__axioms.BetS C b F0) -> ((~(euclidean__axioms.BetS b F0 e)) -> ((euclidean__axioms.Cong b F0 B E) -> ((euclidean__axioms.BetS b D F0) -> ((euclidean__axioms.BetS F0 D b) -> ((euclidean__axioms.Cong F0 D F0 D) -> ((euclidean__defs.Lt F0 D F0 b) -> ((euclidean__axioms.Cong F0 b b F0) -> ((euclidean__defs.Lt F0 D b F0) -> ((euclidean__axioms.Cong D F0 B E) -> ((euclidean__axioms.Cong F0 D B E) -> ((euclidean__defs.Lt B E b F0) -> ((euclidean__axioms.Cong b F0 b e) -> (euclidean__defs.Lt B E b e))))))))))))))))) with (x := F).
-------------------------intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
exact H46.

------------------------- exact H21.
------------------------- exact H1.
------------------------- exact H2.
------------------------- exact H19.
------------------------- exact H20.
------------------------- exact H22.
------------------------- exact H23.
------------------------- exact H24.
------------------------- exact H25.
------------------------- exact H26.
------------------------- exact H27.
------------------------- exact H28.
------------------------- exact H29.
------------------------- exact H30.
------------------------- exact H31.
------------------------- exact H32.
------------------------ assert (* Cut *) (euclidean__defs.Lt B E B E) as H34.
------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence B E b e B E H33 H14).
------------------------- assert (* Cut *) (~(euclidean__defs.Lt B E B E)) as H35.
-------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 B E B E H34).
-------------------------- apply (@H35 H34).
------------ assert (* Cut *) (~(~(euclidean__axioms.BetS b e F))) as H22.
------------- intro H22.
assert (* Cut *) (F = e) as H23.
-------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity C b F e H19 H13 H20 H22).
-------------- apply (@H21 H23).
------------- assert (* Cut *) (euclidean__axioms.BetS C e F) as H23.
-------------- assert (* Cut *) (euclidean__axioms.BetS b e F) as H23.
--------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS b e F) H22).
--------------- apply (@lemma__3__7a.lemma__3__7a C b e F H13 H23).
-------------- assert (* Cut *) (euclidean__axioms.Cong A E C e) as H24.
--------------- assert (* Cut *) (euclidean__axioms.BetS b e F) as H24.
---------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS b e F) H22).
---------------- exact H16.
--------------- assert (* Cut *) (euclidean__axioms.Cong C e A E) as H25.
---------------- assert (* Cut *) (euclidean__axioms.BetS b e F) as H25.
----------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS b e F) H22).
----------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C A E e H24).
---------------- assert (* Cut *) (euclidean__defs.Lt A E C F) as H26.
----------------- assert (* Cut *) (euclidean__axioms.BetS b e F) as H26.
------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS b e F) H22).
------------------ exists e.
split.
------------------- exact H23.
------------------- exact H25.
----------------- exact H26.
Qed.
