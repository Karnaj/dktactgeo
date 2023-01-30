Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__layoff.
Require Export lemma__layoffunique.
Require Export lemma__ray1.
Require Export lemma__ray4.
Require Export logic.
Definition lemma__lessthantransitive : forall A B C D E F, (euclidean__defs.Lt A B C D) -> ((euclidean__defs.Lt C D E F) -> (euclidean__defs.Lt A B E F)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (exists G, (euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B)) as H1 by exact H.
destruct H1 as [G H2].
destruct H2 as [H3 H4].
assert (exists H5, (euclidean__axioms.BetS E H5 F) /\ (euclidean__axioms.Cong E H5 C D)) as H5 by exact H0.
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.neq E H6) as H10.
- assert (* Cut *) ((euclidean__axioms.neq H6 F) /\ ((euclidean__axioms.neq E H6) /\ (euclidean__axioms.neq E F))) as H10.
-- apply (@lemma__betweennotequal.lemma__betweennotequal E H6 F H8).
-- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H13.
- assert (* Cut *) (euclidean__axioms.neq C G) as H11.
-- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H11.
--- apply (@lemma__betweennotequal.lemma__betweennotequal C G D H3).
--- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
-- assert (* Cut *) (exists K, (euclidean__defs.Out E H6 K) /\ (euclidean__axioms.Cong E K C G)) as H12.
--- apply (@lemma__layoff.lemma__layoff E H6 C G H10 H11).
--- destruct H12 as [K H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.Cong E K A B) as H16.
---- apply (@lemma__congruencetransitive.lemma__congruencetransitive E K C G A B H15 H4).
---- assert (* Cut *) ((euclidean__axioms.BetS E K H6) \/ ((H6 = K) \/ (euclidean__axioms.BetS E H6 K))) as H17.
----- apply (@lemma__ray1.lemma__ray1 E H6 K H14).
----- assert (* Cut *) (euclidean__axioms.BetS E K H6) as H18.
------ assert ((euclidean__axioms.BetS E K H6) \/ ((H6 = K) \/ (euclidean__axioms.BetS E H6 K))) as H18 by exact H17.
assert ((euclidean__axioms.BetS E K H6) \/ ((H6 = K) \/ (euclidean__axioms.BetS E H6 K))) as __TmpHyp by exact H18.
destruct __TmpHyp as [H19|H19].
------- exact H19.
------- destruct H19 as [H20|H20].
-------- assert (* Cut *) (euclidean__axioms.Cong C G E K) as H21.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C E K G H15).
--------- assert (* Cut *) (euclidean__axioms.Cong C G E H6) as H22.
---------- apply (@eq__ind__r euclidean__axioms.Point K (fun H22 => (euclidean__axioms.BetS E H22 F) -> ((euclidean__axioms.Cong E H22 C D) -> ((euclidean__axioms.neq E H22) -> ((euclidean__defs.Out E H22 K) -> (euclidean__axioms.Cong C G E H22)))))) with (x := H6).
-----------intro H22.
intro H23.
intro H24.
intro H25.
exact H21.

----------- exact H20.
----------- exact H8.
----------- exact H9.
----------- exact H10.
----------- exact H14.
---------- assert (* Cut *) (euclidean__axioms.Cong C G C D) as H23.
----------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C G E H6 C D H22 H9).
----------- assert (* Cut *) (euclidean__defs.Out C G D) as H24.
------------ apply (@lemma__ray4.lemma__ray4 C G D).
-------------right.
right.
exact H3.

------------- exact H11.
------------ assert (* Cut *) (G = G) as H25.
------------- apply (@logic.eq__refl Point G).
------------- assert (* Cut *) (euclidean__defs.Out C G G) as H26.
-------------- apply (@lemma__ray4.lemma__ray4 C G G).
---------------right.
left.
exact H25.

--------------- exact H11.
-------------- assert (* Cut *) (~(~(euclidean__axioms.BetS E K H6))) as H27.
--------------- intro H27.
assert (* Cut *) (G = D) as H28.
---------------- apply (@lemma__layoffunique.lemma__layoffunique C G G D H26 H24 H23).
---------------- assert (* Cut *) (euclidean__axioms.neq G D) as H29.
----------------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H29.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C G D H3).
------------------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
----------------- apply (@H29 H28).
--------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E K H6)).
----------------intro H28.
assert (* Cut *) (False) as H29.
----------------- apply (@H27 H28).
----------------- contradiction H29.

-------- assert (* Cut *) (euclidean__axioms.Cong C D E H6) as H21.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C E H6 D H9).
--------- assert (* Cut *) (euclidean__axioms.Cong C G E K) as H22.
---------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C E K G H15).
---------- assert (* Cut *) (euclidean__axioms.neq C D) as H23.
----------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H23.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal C G D H3).
------------ destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H27.
----------- assert (* Cut *) (euclidean__axioms.neq H6 K) as H24.
------------ assert (* Cut *) ((euclidean__axioms.neq H6 K) /\ ((euclidean__axioms.neq E H6) /\ (euclidean__axioms.neq E K))) as H24.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H6 K H20).
------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
------------ assert (* Cut *) (exists J, (euclidean__axioms.BetS C D J) /\ (euclidean__axioms.Cong D J H6 K)) as H25.
------------- apply (@lemma__extension.lemma__extension C D H6 K H23 H24).
------------- destruct H25 as [J H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__defs.Out C D J) as H29.
-------------- apply (@lemma__ray4.lemma__ray4 C D J).
---------------right.
right.
exact H27.

--------------- exact H23.
-------------- assert (* Cut *) (euclidean__defs.Out C D G) as H30.
--------------- apply (@lemma__ray4.lemma__ray4 C D G).
----------------left.
exact H3.

---------------- exact H23.
--------------- assert (* Cut *) (euclidean__axioms.Cong C J E K) as H31.
---------------- apply (@euclidean__axioms.cn__sumofparts C D J E H6 K H21 H28 H27 H20).
---------------- assert (* Cut *) (euclidean__axioms.Cong C J C G) as H32.
----------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C J E K C G H31 H15).
----------------- assert (* Cut *) (J = G) as H33.
------------------ apply (@lemma__layoffunique.lemma__layoffunique C D J G H29 H30 H32).
------------------ assert (* Cut *) (euclidean__axioms.BetS G D J) as H34.
------------------- apply (@lemma__3__6a.lemma__3__6a C G D J H3 H27).
------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS E K H6))) as H35.
-------------------- intro H35.
assert (* Cut *) (euclidean__axioms.neq G J) as H36.
--------------------- assert (* Cut *) ((euclidean__axioms.neq D J) /\ ((euclidean__axioms.neq G D) /\ (euclidean__axioms.neq G J))) as H36.
---------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G D J H34).
---------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H40.
--------------------- assert (* Cut *) (euclidean__axioms.neq J G) as H37.
---------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun J0 => (euclidean__axioms.BetS C D J0) -> ((euclidean__axioms.Cong D J0 H6 K) -> ((euclidean__defs.Out C D J0) -> ((euclidean__axioms.Cong C J0 E K) -> ((euclidean__axioms.Cong C J0 C G) -> ((euclidean__axioms.BetS G D J0) -> ((euclidean__axioms.neq G J0) -> (euclidean__axioms.neq J0 G))))))))) with (x := J).
-----------------------intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
exact H43.

----------------------- exact H33.
----------------------- exact H27.
----------------------- exact H28.
----------------------- exact H29.
----------------------- exact H31.
----------------------- exact H32.
----------------------- exact H34.
----------------------- exact H36.
---------------------- apply (@H37 H33).
-------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS E K H6)).
---------------------intro H36.
assert (* Cut *) (False) as H37.
---------------------- apply (@H35 H36).
---------------------- contradiction H37.

------ assert (* Cut *) (euclidean__axioms.BetS E K F) as H19.
------- apply (@lemma__3__6b.lemma__3__6b E K H6 F H18 H8).
------- assert (* Cut *) (euclidean__defs.Lt A B E F) as H20.
-------- exists K.
split.
--------- exact H19.
--------- exact H16.
-------- exact H20.
Qed.
