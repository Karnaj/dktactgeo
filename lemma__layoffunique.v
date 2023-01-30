Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__differenceofparts.
Require Export lemma__equalitysymmetric.
Require Export lemma__extensionunique.
Require Export lemma__interior5.
Require Export lemma__partnotequalwhole.
Require Export lemma__ray1.
Require Export logic.
Definition lemma__layoffunique : forall A B C D, (euclidean__defs.Out A B C) -> ((euclidean__defs.Out A B D) -> ((euclidean__axioms.Cong A C A D) -> (C = D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.Cong A D A C) as H2.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A C D H1).
- assert (* Cut *) ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as H3.
-- apply (@lemma__ray1.lemma__ray1 A B C H).
-- assert (* Cut *) ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as H4.
--- apply (@lemma__ray1.lemma__ray1 A B D H0).
--- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H5.
---- apply (@euclidean__axioms.cn__congruencereflexive A B).
---- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H6.
----- apply (@euclidean__axioms.cn__congruencereflexive B C).
----- assert (* Cut *) (euclidean__axioms.Cong C B C B) as H7.
------ apply (@euclidean__axioms.cn__congruencereflexive C B).
------ assert (* Cut *) (euclidean__axioms.Cong A C A C) as H8.
------- apply (@euclidean__axioms.cn__congruencereflexive A C).
------- assert (* Cut *) (C = D) as H9.
-------- assert ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as H9 by exact H3.
assert ((euclidean__axioms.BetS A C B) \/ ((B = C) \/ (euclidean__axioms.BetS A B C))) as __TmpHyp by exact H9.
destruct __TmpHyp as [H10|H10].
--------- assert (* Cut *) (C = D) as H11.
---------- assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as H11 by exact H4.
assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as __TmpHyp0 by exact H11.
destruct __TmpHyp0 as [H12|H12].
----------- assert (* Cut *) (euclidean__axioms.Cong C B D B) as H13.
------------ apply (@lemma__differenceofparts.lemma__differenceofparts A C B A D B H1 H5 H10 H12).
------------ assert (* Cut *) (euclidean__axioms.Cong B C B D) as H14.
------------- assert (* Cut *) ((euclidean__axioms.Cong B C B D) /\ ((euclidean__axioms.Cong B C D B) /\ (euclidean__axioms.Cong C B B D))) as H14.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip C B D B H13).
-------------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
------------- assert (* Cut *) (euclidean__axioms.Cong C C C D) as H15.
-------------- apply (@lemma__interior5.lemma__interior5 A C B C A C B D H10 H10 H8 H7 H1 H14).
-------------- assert (* Cut *) (euclidean__axioms.Cong C D C C) as H16.
--------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C C C D H15).
--------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H17.
---------------- intro H17.
assert (* Cut *) (euclidean__axioms.neq C C) as H18.
----------------- apply (@euclidean__axioms.axiom__nocollapse C D C C H17 H16).
----------------- assert (* Cut *) (C = C) as H19.
------------------ assert (* Cut *) (False) as H19.
------------------- assert (* Cut *) (C = C) as H19.
-------------------- apply (@logic.eq__refl Point C).
-------------------- apply (@H18 H19).
------------------- assert (False) as H20 by exact H19.
apply (@logic.eq__refl Point C).
------------------ apply (@H18 H19).
---------------- apply (@euclidean__tactics.NNPP (C = D)).
-----------------intro H18.
assert (* Cut *) (False) as H19.
------------------ apply (@H17 H18).
------------------ contradiction H19.

----------- destruct H12 as [H13|H13].
------------ assert (* Cut *) (euclidean__axioms.BetS A C D) as H14.
------------- apply (@eq__ind__r euclidean__axioms.Point D (fun B0 => (euclidean__defs.Out A B0 C) -> ((euclidean__defs.Out A B0 D) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 C B0 C) -> ((euclidean__axioms.Cong C B0 C B0) -> ((euclidean__axioms.BetS A C B0) -> (euclidean__axioms.BetS A C D)))))))) with (x := B).
--------------intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
exact H19.

-------------- exact H13.
-------------- exact H.
-------------- exact H0.
-------------- exact H5.
-------------- exact H6.
-------------- exact H7.
-------------- exact H10.
------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H15.
-------------- intro H15.
assert (* Cut *) (~(euclidean__axioms.Cong A C A D)) as H16.
--------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A C D H14).
--------------- apply (@H16 H1).
-------------- apply (@euclidean__tactics.NNPP (C = D)).
---------------intro H16.
assert (* Cut *) (False) as H17.
---------------- apply (@H15 H16).
---------------- contradiction H17.

------------ assert (* Cut *) (euclidean__axioms.BetS A C D) as H14.
------------- apply (@lemma__3__6b.lemma__3__6b A C B D H10 H13).
------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H15.
-------------- intro H15.
assert (* Cut *) (~(euclidean__axioms.Cong A C A D)) as H16.
--------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A C D H14).
--------------- apply (@H16 H1).
-------------- apply (@euclidean__tactics.NNPP (C = D)).
---------------intro H16.
assert (* Cut *) (False) as H17.
---------------- apply (@H15 H16).
---------------- contradiction H17.

---------- exact H11.
--------- destruct H10 as [H11|H11].
---------- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H12.
----------- apply (@eq__ind__r euclidean__axioms.Point C (fun B0 => (euclidean__defs.Out A B0 C) -> ((euclidean__defs.Out A B0 D) -> (((euclidean__axioms.BetS A D B0) \/ ((B0 = D) \/ (euclidean__axioms.BetS A B0 D))) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 C B0 C) -> ((euclidean__axioms.Cong C B0 C B0) -> (euclidean__axioms.Cong A B0 A D)))))))) with (x := B).
------------intro H12.
intro H13.
intro H14.
intro H15.
intro H16.
intro H17.
exact H1.

------------ exact H11.
------------ exact H.
------------ exact H0.
------------ exact H4.
------------ exact H5.
------------ exact H6.
------------ exact H7.
----------- assert (* Cut *) (euclidean__axioms.Cong A D A B) as H13.
------------ apply (@eq__ind__r euclidean__axioms.Point C (fun B0 => (euclidean__defs.Out A B0 C) -> ((euclidean__defs.Out A B0 D) -> (((euclidean__axioms.BetS A D B0) \/ ((B0 = D) \/ (euclidean__axioms.BetS A B0 D))) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 C B0 C) -> ((euclidean__axioms.Cong C B0 C B0) -> ((euclidean__axioms.Cong A B0 A D) -> (euclidean__axioms.Cong A D A B0))))))))) with (x := B).
-------------intro H13.
intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
exact H2.

------------- exact H11.
------------- exact H.
------------- exact H0.
------------- exact H4.
------------- exact H5.
------------- exact H6.
------------- exact H7.
------------- exact H12.
------------ assert (* Cut *) (C = D) as H14.
------------- assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as H14 by exact H4.
assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as __TmpHyp0 by exact H14.
destruct __TmpHyp0 as [H15|H15].
-------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H16.
--------------- intro H16.
assert (* Cut *) (~(euclidean__axioms.Cong A D A B)) as H17.
---------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A D B H15).
---------------- apply (@H17 H13).
--------------- apply (@euclidean__tactics.NNPP (C = D)).
----------------intro H17.
assert (* Cut *) (False) as H18.
----------------- apply (@H16 H17).
----------------- contradiction H18.

-------------- destruct H15 as [H16|H16].
--------------- assert (* Cut *) (C = B) as H17.
---------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric C B H11).
---------------- assert (* Cut *) (D = B) as H18.
----------------- apply (@eq__ind euclidean__axioms.Point B (fun C0 => (euclidean__defs.Out A B C0) -> ((euclidean__axioms.Cong A C0 A D) -> ((euclidean__axioms.Cong A D A C0) -> ((euclidean__axioms.Cong B C0 B C0) -> ((euclidean__axioms.Cong C0 B C0 B) -> ((euclidean__axioms.Cong A C0 A C0) -> ((C0 = B) -> (D = B))))))))) with (y := C).
------------------intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
apply (@eq__ind__r euclidean__axioms.Point D (fun B0 => (euclidean__defs.Out A B0 B0) -> ((euclidean__defs.Out A B0 D) -> ((euclidean__axioms.Cong A D A B0) -> ((euclidean__axioms.Cong A B0 A D) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 B0 B0 B0) -> ((euclidean__axioms.Cong B0 B0 B0 B0) -> ((euclidean__axioms.Cong A B0 A D) -> ((euclidean__axioms.Cong A D A B0) -> ((B0 = B0) -> (D = B0))))))))))))) with (x := B).
-------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
exact H35.

------------------- exact H16.
------------------- exact H18.
------------------- exact H0.
------------------- exact H20.
------------------- exact H19.
------------------- exact H5.
------------------- exact H23.
------------------- exact H22.
------------------- exact H21.
------------------- exact H12.
------------------- exact H13.
------------------- exact H24.

------------------ exact H11.
------------------ exact H.
------------------ exact H1.
------------------ exact H2.
------------------ exact H6.
------------------ exact H7.
------------------ exact H8.
------------------ exact H17.
----------------- assert (* Cut *) (C = D) as H19.
------------------ apply (@eq__ind euclidean__axioms.Point B (fun D0 => (euclidean__defs.Out A B D0) -> ((euclidean__axioms.Cong A C A D0) -> ((euclidean__axioms.Cong A D0 A C) -> ((euclidean__axioms.Cong A B A D0) -> ((euclidean__axioms.Cong A D0 A B) -> ((D0 = B) -> (C = D0)))))))) with (y := D).
-------------------intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
apply (@eq__ind euclidean__axioms.Point B (fun C0 => (euclidean__defs.Out A B C0) -> ((euclidean__axioms.Cong A B A C0) -> ((euclidean__axioms.Cong A C0 A B) -> ((euclidean__axioms.Cong B C0 B C0) -> ((euclidean__axioms.Cong C0 B C0 B) -> ((euclidean__axioms.Cong A C0 A C0) -> ((C0 = B) -> ((B = B) -> (C0 = B)))))))))) with (y := C).
--------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
assert (B = B) as H32 by exact H31.
intro H33.
exact H33.

-------------------- exact H11.
-------------------- exact H.
-------------------- exact H21.
-------------------- exact H20.
-------------------- exact H6.
-------------------- exact H7.
-------------------- exact H8.
-------------------- exact H17.
-------------------- exact H24.

------------------- exact H16.
------------------- exact H0.
------------------- exact H1.
------------------- exact H2.
------------------- exact H12.
------------------- exact H13.
------------------- exact H18.
------------------ exact H19.
--------------- assert (* Cut *) (euclidean__axioms.BetS A C D) as H17.
---------------- apply (@eq__ind__r euclidean__axioms.Point C (fun B0 => (euclidean__defs.Out A B0 C) -> ((euclidean__defs.Out A B0 D) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 C B0 C) -> ((euclidean__axioms.Cong C B0 C B0) -> ((euclidean__axioms.Cong A B0 A D) -> ((euclidean__axioms.Cong A D A B0) -> ((euclidean__axioms.BetS A B0 D) -> (euclidean__axioms.BetS A C D)))))))))) with (x := B).
-----------------intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
exact H24.

----------------- exact H11.
----------------- exact H.
----------------- exact H0.
----------------- exact H5.
----------------- exact H6.
----------------- exact H7.
----------------- exact H12.
----------------- exact H13.
----------------- exact H16.
---------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H18.
----------------- intro H18.
assert (* Cut *) (~(euclidean__axioms.Cong A C A D)) as H19.
------------------ apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A C D H17).
------------------ apply (@H19 H1).
----------------- apply (@euclidean__tactics.NNPP (C = D)).
------------------intro H19.
assert (* Cut *) (False) as H20.
------------------- apply (@H18 H19).
------------------- contradiction H20.

------------- exact H14.
---------- assert (* Cut *) (C = D) as H12.
----------- assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as H12 by exact H4.
assert ((euclidean__axioms.BetS A D B) \/ ((B = D) \/ (euclidean__axioms.BetS A B D))) as __TmpHyp0 by exact H12.
destruct __TmpHyp0 as [H13|H13].
------------ assert (* Cut *) (euclidean__axioms.BetS A D C) as H14.
------------- apply (@lemma__3__6b.lemma__3__6b A D B C H13 H11).
------------- assert (euclidean__axioms.Cong A D A C) as H15 by exact H2.
assert (* Cut *) (~(euclidean__axioms.neq C D)) as H16.
-------------- intro H16.
assert (* Cut *) (~(euclidean__axioms.Cong A D A C)) as H17.
--------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A D C H14).
--------------- apply (@H17 H15).
-------------- apply (@euclidean__tactics.NNPP (C = D)).
---------------intro H17.
assert (* Cut *) (False) as H18.
---------------- apply (@H16 H17).
---------------- contradiction H18.

------------ destruct H13 as [H14|H14].
------------- assert (* Cut *) (euclidean__axioms.BetS A D C) as H15.
-------------- apply (@eq__ind__r euclidean__axioms.Point D (fun B0 => (euclidean__defs.Out A B0 C) -> ((euclidean__defs.Out A B0 D) -> ((euclidean__axioms.Cong A B0 A B0) -> ((euclidean__axioms.Cong B0 C B0 C) -> ((euclidean__axioms.Cong C B0 C B0) -> ((euclidean__axioms.BetS A B0 C) -> (euclidean__axioms.BetS A D C)))))))) with (x := B).
---------------intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
exact H20.

--------------- exact H14.
--------------- exact H.
--------------- exact H0.
--------------- exact H5.
--------------- exact H6.
--------------- exact H7.
--------------- exact H11.
-------------- assert (* Cut *) (~(euclidean__axioms.neq C D)) as H16.
--------------- intro H16.
assert (* Cut *) (~(euclidean__axioms.Cong A D A C)) as H17.
---------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole A D C H15).
---------------- apply (@H17 H2).
--------------- apply (@euclidean__tactics.NNPP (C = D)).
----------------intro H17.
assert (* Cut *) (False) as H18.
----------------- apply (@H16 H17).
----------------- contradiction H18.

------------- assert (* Cut *) (euclidean__axioms.neq A B) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H15.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal A B D H14).
--------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H18.
-------------- assert (* Cut *) (euclidean__axioms.Cong B C B D) as H16.
--------------- apply (@lemma__differenceofparts.lemma__differenceofparts A B C A B D H5 H1 H11 H14).
--------------- assert (* Cut *) (C = D) as H17.
---------------- apply (@lemma__extensionunique.lemma__extensionunique A B C D H11 H14 H16).
---------------- exact H17.
----------- exact H12.
-------- exact H9.
Qed.
