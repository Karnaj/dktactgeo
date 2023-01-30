Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__Playfairhelper2.
Require Export lemma__betweennotequal.
Require Export lemma__crisscross.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export logic.
Definition lemma__Playfair : forall A B C D E, (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par A B C E) -> (euclidean__axioms.Col C D E)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A B) as H1.
- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H1 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H1.
destruct __TmpHyp as [x H2].
destruct H2 as [x0 H3].
destruct H3 as [x1 H4].
destruct H4 as [x2 H5].
destruct H5 as [x3 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H27 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H27.
destruct __TmpHyp0 as [x4 H28].
destruct H28 as [x5 H29].
destruct H29 as [x6 H30].
destruct H30 as [x7 H31].
destruct H31 as [x8 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H33.
- assert (* Cut *) (euclidean__axioms.neq C D) as H2.
-- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H2.
destruct __TmpHyp as [x H3].
destruct H3 as [x0 H4].
destruct H4 as [x1 H5].
destruct H5 as [x2 H6].
destruct H6 as [x3 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H28 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H28.
destruct __TmpHyp0 as [x4 H29].
destruct H29 as [x5 H30].
destruct H30 as [x6 H31].
destruct H31 as [x7 H32].
destruct H32 as [x8 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H36.
-- assert (* Cut *) (~(~((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)))) as H3.
--- intro H3.
assert (* Cut *) (euclidean__defs.Par A B D C) as H4.
---- assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H4.
----- apply (@lemma__parallelflip.lemma__parallelflip A B C D H).
----- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H7.
---- assert (* Cut *) (euclidean__defs.CR A C D B) as H5.
----- apply (@lemma__crisscross.lemma__crisscross A D B C H4).
------intro H5.
apply (@H3).
-------left.
exact H5.


----- assert (exists p, (euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS D p B)) as H6 by exact H5.
destruct H6 as [p H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.neq D B) as H10.
------ assert (* Cut *) ((euclidean__axioms.neq p B) /\ ((euclidean__axioms.neq D p) /\ (euclidean__axioms.neq D B))) as H10.
------- apply (@lemma__betweennotequal.lemma__betweennotequal D p B H9).
------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H14.
------ assert (* Cut *) (euclidean__axioms.neq B D) as H11.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D B H10).
------- assert (* Cut *) (euclidean__axioms.BetS B p D) as H12.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry D p B H9).
-------- assert (* Cut *) (euclidean__defs.CR A C B D) as H13.
--------- exists p.
split.
---------- exact H8.
---------- exact H12.
--------- apply (@H3).
----------right.
exact H13.

--- assert (* Cut *) (euclidean__axioms.Col C D E) as H4.
---- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H4.
----- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D))).
------intro H4.
assert (* Cut *) (False) as H5.
------- apply (@H3 H4).
------- assert (* Cut *) ((euclidean__defs.CR A D B C) -> False) as H6.
-------- intro H6.
apply (@H4).
---------left.
exact H6.

-------- assert (* Cut *) ((euclidean__defs.CR A C B D) -> False) as H7.
--------- intro H7.
apply (@H4).
----------right.
exact H7.

--------- contradiction H5.

----- assert ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H5 by exact H4.
assert ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as __TmpHyp by exact H5.
destruct __TmpHyp as [H6|H6].
------ assert (* Cut *) (euclidean__axioms.Col C D E) as H7.
------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H7.
-------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
-------- apply (@euclidean__tactics.not__nCol__Col C D E).
---------intro H8.
apply (@euclidean__tactics.Col__nCol__False C D E H8).
----------apply (@lemma__Playfairhelper2.lemma__Playfairhelper2 A B C D E H H0 H6).


------- exact H7.
------ assert (exists p, (euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS B p D)) as H7 by exact H6.
destruct H7 as [p H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__defs.CR B D A C) as H11.
------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H11.
-------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
-------- exists p.
split.
--------- exact H10.
--------- exact H9.
------- assert (* Cut *) (euclidean__defs.Par B A C D) as H12.
-------- assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H12.
--------- apply (@lemma__parallelflip.lemma__parallelflip A B C D H).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H13.
-------- assert (* Cut *) (euclidean__defs.Par B A C E) as H13.
--------- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H13.
---------- apply (@lemma__parallelflip.lemma__parallelflip A B C E H0).
---------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.Col C D E) as H14.
---------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H14.
----------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
----------- apply (@euclidean__tactics.not__nCol__Col C D E).
------------intro H15.
apply (@euclidean__tactics.Col__nCol__False C D E H15).
-------------apply (@lemma__Playfairhelper2.lemma__Playfairhelper2 B A C D E H12 H13 H11).


---------- exact H14.
---- exact H4.
Qed.
