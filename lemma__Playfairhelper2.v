Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__Playfairhelper.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crisscross.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__Playfairhelper2 : forall A B C D E, (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par A B C E) -> ((euclidean__defs.CR A D B C) -> (euclidean__axioms.Col C D E))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq A B) as H2.
- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2 by exact H0.
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
exact H34.
- assert (* Cut *) (euclidean__axioms.neq C D) as H3.
-- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H3 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H3.
destruct __TmpHyp as [x H4].
destruct H4 as [x0 H5].
destruct H5 as [x1 H6].
destruct H6 as [x2 H7].
destruct H7 as [x3 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H29.
destruct __TmpHyp0 as [x4 H30].
destruct H30 as [x5 H31].
destruct H31 as [x6 H32].
destruct H32 as [x7 H33].
destruct H33 as [x8 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H37.
-- assert (* Cut *) (~(~((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)))) as H4.
--- intro H4.
assert (* Cut *) (euclidean__defs.Par A B E C) as H5.
---- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H5.
----- apply (@lemma__parallelflip.lemma__parallelflip A B C E H0).
----- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H8.
---- assert (* Cut *) (euclidean__defs.CR A C E B) as H6.
----- apply (@lemma__crisscross.lemma__crisscross A E B C H5).
------intro H6.
apply (@H4).
-------left.
exact H6.


----- apply (@H4).
------right.
exact H6.

--- assert (exists M, (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C)) as H5 by exact H1.
destruct H5 as [M H6].
destruct H6 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Col C D E) as H9.
---- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H9.
----- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B))).
------intro H9.
assert (* Cut *) (False) as H10.
------- apply (@H4 H9).
------- assert (* Cut *) ((euclidean__defs.CR A E B C) -> False) as H11.
-------- intro H11.
apply (@H9).
---------left.
exact H11.

-------- assert (* Cut *) ((euclidean__defs.CR A C E B) -> False) as H12.
--------- intro H12.
apply (@H9).
----------right.
exact H12.

--------- contradiction H10.

----- assert ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H10 by exact H9.
assert ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as __TmpHyp by exact H10.
destruct __TmpHyp as [H11|H11].
------ assert (* Cut *) (euclidean__axioms.Col C D E) as H12.
------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H12.
-------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------- apply (@euclidean__tactics.not__nCol__Col C D E).
---------intro H13.
apply (@euclidean__tactics.Col__nCol__False C D E H13).
----------apply (@lemma__Playfairhelper.lemma__Playfairhelper A B C D E H H0 H1 H11).


------- exact H12.
------ assert (exists m, (euclidean__axioms.BetS A m C) /\ (euclidean__axioms.BetS E m B)) as H12 by exact H11.
destruct H12 as [m H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.BetS B m E) as H16.
------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H16.
-------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry E m B H15).
------- assert (* Cut *) (euclidean__axioms.neq C E) as H17.
-------- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H17 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H17.
destruct __TmpHyp0 as [x H18].
destruct H18 as [x0 H19].
destruct H19 as [x1 H20].
destruct H20 as [x2 H21].
destruct H21 as [x3 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H43 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H43.
destruct __TmpHyp1 as [x4 H44].
destruct H44 as [x5 H45].
destruct H45 as [x6 H46].
destruct H46 as [x7 H47].
destruct H47 as [x8 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H25.
-------- assert (* Cut *) (euclidean__axioms.neq E C) as H18.
--------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H18.
---------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C E H17).
--------- assert (* Cut *) (exists e, (euclidean__axioms.BetS E C e) /\ (euclidean__axioms.Cong C e E C)) as H19.
---------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H19.
----------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------- apply (@lemma__extension.lemma__extension E C E C H18 H18).
---------- destruct H19 as [e H20].
destruct H20 as [H21 H22].
assert (* Cut *) (euclidean__axioms.Col E C e) as H23.
----------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H23.
------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------ right.
right.
right.
right.
left.
exact H21.
----------- assert (* Cut *) (euclidean__axioms.neq C e) as H24.
------------ assert (* Cut *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H24.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal E C e H21).
------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
------------ assert (* Cut *) (euclidean__axioms.neq e C) as H25.
------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H25.
-------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C e H24).
------------- assert (* Cut *) (euclidean__defs.Par A B E C) as H26.
-------------- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H26.
--------------- apply (@lemma__parallelflip.lemma__parallelflip A B C E H0).
--------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H29.
-------------- assert (* Cut *) (euclidean__defs.Par A B e C) as H27.
--------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H27.
---------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B e E C H26 H23 H25).
--------------- assert (* Cut *) (euclidean__defs.Par A B C e) as H28.
---------------- assert (* Cut *) ((euclidean__defs.Par B A e C) /\ ((euclidean__defs.Par A B C e) /\ (euclidean__defs.Par B A C e))) as H28.
----------------- apply (@lemma__parallelflip.lemma__parallelflip A B e C H27).
----------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
---------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H29.
----------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H29.
------------------ apply (@lemma__parallelNC.lemma__parallelNC A B C D H).
------------------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H32.
----------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H30.
------------------ assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C e) /\ ((euclidean__axioms.nCol B C e) /\ (euclidean__axioms.nCol A B e)))) as H30.
------------------- apply (@lemma__parallelNC.lemma__parallelNC A B C e H28).
------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H31.
------------------ assert (* Cut *) (euclidean__axioms.nCol B C A) as H31.
------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H31.
-------------------- apply (@lemma__NCorder.lemma__NCorder A B C H30).
-------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H34.
------------------- assert (* Cut *) (exists H32, (euclidean__axioms.BetS B H32 m) /\ (euclidean__axioms.BetS A H32 M)) as H32.
-------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H32.
--------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------- apply (@euclidean__axioms.postulate__Pasch__inner B A C M m H8 H14 H31).
-------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
assert (* Cut *) (euclidean__axioms.nCol A E C) as H37.
--------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H37.
---------------------- apply (@lemma__parallelNC.lemma__parallelNC A B E C H26).
---------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H40.
--------------------- assert (* Cut *) (euclidean__axioms.Col E C e) as H38.
---------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H38.
----------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------- exact H23.
---------------------- assert (* Cut *) (euclidean__axioms.Col C E e) as H39.
----------------------- assert (* Cut *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H39.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder E C e H38).
------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H40.
----------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H40.
------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H40.
------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------- exact H17.
------------------------ assert (* Cut *) (euclidean__axioms.nCol C E A) as H41.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H41.
-------------------------- apply (@lemma__NCorder.lemma__NCorder A E C H37).
-------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
------------------------- assert (* Cut *) (E = E) as H42.
-------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H42.
--------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------- apply (@logic.eq__refl Point E).
-------------------------- assert (* Cut *) (euclidean__axioms.Col C E E) as H43.
--------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H43.
---------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------- right.
right.
left.
exact H42.
--------------------------- assert (* Cut *) (euclidean__axioms.neq E e) as H44.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H44.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E C e H21).
----------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H48.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol E e A) as H45.
----------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H45.
------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------ apply (@euclidean__tactics.nCol__notCol E e A).
-------------------------------apply (@euclidean__tactics.nCol__not__Col E e A).
--------------------------------apply (@lemma__NChelper.lemma__NChelper C E A E e H41 H43 H39 H44).


----------------------------- assert (* Cut *) (exists F, (euclidean__axioms.BetS A F e) /\ (euclidean__axioms.BetS E m F)) as H46.
------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H46.
------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer A E C m e H14 H21 H45).
------------------------------ destruct H46 as [F H47].
destruct H47 as [H48 H49].
assert (* Cut *) (euclidean__axioms.BetS e F A) as H50.
------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H50.
-------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A F e H48).
------------------------------- assert (* Cut *) (euclidean__axioms.Col E m F) as H51.
-------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H51.
--------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------- right.
right.
right.
right.
left.
exact H49.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col E m B) as H52.
--------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H52.
---------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------- right.
right.
right.
right.
left.
exact H15.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col m E F) as H53.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H53.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E m F H51).
----------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H54.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col m E B) as H54.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E B) /\ ((euclidean__axioms.Col m B E) /\ ((euclidean__axioms.Col B E m) /\ ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E))))) as H54.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E m B H52).
------------------------------------ destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H55.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H55.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H55.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E m F H49).
------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H58.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq m E) as H56.
------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H56.
-------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E m H55).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F B) as H57.
-------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H57.
--------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col E F B).
----------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False E F B H58).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 m E F B H53 H54 H56).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B F) as H58.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))))) as H58.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F B H57).
---------------------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq e E) as H59.
---------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H59.
----------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E e H44).
---------------------------------------- assert (* Cut *) (E = E) as H60.
----------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H60.
------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------ exact H42.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col e E E) as H61.
------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H61.
------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------- right.
right.
left.
exact H60.
------------------------------------------ assert (* Cut *) (B = B) as H62.
------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H62.
-------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------- apply (@logic.eq__refl Point B).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B B A) as H63.
-------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H63.
--------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------- left.
exact H62.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H64.
--------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H64.
---------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H2).
--------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C E) as H65.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B A C e) /\ ((euclidean__defs.Par A B e C) /\ (euclidean__defs.Par B A e C))) as H65.
----------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A B C e H28).
----------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H0.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E e) as H66.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B B A) /\ ((euclidean__axioms.Col B A B) /\ ((euclidean__axioms.Col A B B) /\ ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B))))) as H66.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B B A H63).
------------------------------------------------ destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H39.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B e E) as H67.
------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H67.
------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B e C E H65 H66 H59).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Par e E A B) as H68.
------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H68.
-------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B e E H67).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Par e E B A) as H69.
-------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E e A B) /\ ((euclidean__defs.Par e E B A) /\ (euclidean__defs.Par E e B A))) as H69.
--------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip e E A B H68).
--------------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H72.
-------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet e E B A)) as H70.
--------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H70 by exact H69.
assert (exists U V u v X, (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H70.
destruct __TmpHyp0 as [x H71].
destruct H71 as [x0 H72].
destruct H72 as [x1 H73].
destruct H73 as [x2 H74].
destruct H74 as [x3 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
assert (exists U V u v X, (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H96 by exact H68.
assert (exists U V u v X, (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H96.
destruct __TmpHyp1 as [x4 H97].
destruct H97 as [x5 H98].
destruct H98 as [x6 H99].
destruct H99 as [x7 H100].
destruct H100 as [x8 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H122 by exact H67.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H122.
destruct __TmpHyp2 as [x9 H123].
destruct H123 as [x10 H124].
destruct H124 as [x11 H125].
destruct H125 as [x12 H126].
destruct H126 as [x13 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H148 by exact H65.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H148.
destruct __TmpHyp3 as [x14 H149].
destruct H149 as [x15 H150].
destruct H150 as [x16 H151].
destruct H151 as [x17 H152].
destruct H152 as [x18 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H174 by exact H28.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H174.
destruct __TmpHyp4 as [x19 H175].
destruct H175 as [x20 H176].
destruct H176 as [x21 H177].
destruct H177 as [x22 H178].
destruct H178 as [x23 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H200 by exact H27.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H200.
destruct __TmpHyp5 as [x24 H201].
destruct H201 as [x25 H202].
destruct H202 as [x26 H203].
destruct H203 as [x27 H204].
destruct H204 as [x28 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H226 by exact H26.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H226.
destruct __TmpHyp6 as [x29 H227].
destruct H227 as [x30 H228].
destruct H228 as [x31 H229].
destruct H229 as [x32 H230].
destruct H230 as [x33 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
destruct H235 as [H236 H237].
destruct H237 as [H238 H239].
destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
destruct H249 as [H250 H251].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H252 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H252.
destruct __TmpHyp7 as [x34 H253].
destruct H253 as [x35 H254].
destruct H254 as [x36 H255].
destruct H255 as [x37 H256].
destruct H256 as [x38 H257].
destruct H257 as [H258 H259].
destruct H259 as [H260 H261].
destruct H261 as [H262 H263].
destruct H263 as [H264 H265].
destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H278 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H278.
destruct __TmpHyp8 as [x39 H279].
destruct H279 as [x40 H280].
destruct H280 as [x41 H281].
destruct H281 as [x42 H282].
destruct H282 as [x43 H283].
destruct H283 as [H284 H285].
destruct H285 as [H286 H287].
destruct H287 as [H288 H289].
destruct H289 as [H290 H291].
destruct H291 as [H292 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
exact H92.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F B) as H71.
---------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H71.
----------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween e E B A E B F H61 H63 H59 H64 H59 H64 H70 H50 H58).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B F E) as H72.
----------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H72.
------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry E F B H71).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e C E) as H73.
------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H73.
------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E C e H21).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B E C) as H74.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H74.
-------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B E C H26).
-------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H79.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E C B) as H75.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))))) as H75.
--------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B E C H74).
--------------------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H78.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C e) as H76.
--------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H76.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------- exact H38.
--------------------------------------------------------- assert (* Cut *) (E = E) as H77.
---------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H77.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------------- exact H60.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C E) as H78.
----------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H78.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------ right.
left.
exact H77.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E e B) as H79.
------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H79.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol E e B).
--------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col E e B).
---------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper E C B E e H75 H78 H76 H44).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B E e) as H80.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol e E B) /\ ((euclidean__axioms.nCol e B E) /\ ((euclidean__axioms.nCol B E e) /\ ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E))))) as H80.
-------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E e B H79).
-------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H85.
------------------------------------------------------------- assert (* Cut *) (exists K, (euclidean__axioms.BetS B K C) /\ (euclidean__axioms.BetS e K F)) as H81.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H81.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner B e E F C H72 H73 H80).
-------------------------------------------------------------- destruct H81 as [K H82].
destruct H82 as [H83 H84].
assert (* Cut *) (euclidean__axioms.BetS e F A) as H85.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H85.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------------- exact H50.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e K A) as H86.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H86.
----------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b e K F A H84 H85).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A K e) as H87.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H87.
------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry e K A H86).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A e) as H88.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H88.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A K e H87).
------------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H92.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CR A e B C) as H89.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H89.
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------------------- exists K.
split.
--------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------- exact H83.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D e) as H90.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H90.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C D e).
----------------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False C D e H91).
-----------------------------------------------------------------------apply (@lemma__Playfairhelper.lemma__Playfairhelper A B C D e H H28 H1 H89).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C D) as H91.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C e) /\ ((euclidean__axioms.Col D e C) /\ ((euclidean__axioms.Col e C D) /\ ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C))))) as H91.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D e H90).
---------------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H96.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C E) as H92.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H92.
----------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E C e H76).
----------------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H100.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H93.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H93.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A K e H87).
------------------------------------------------------------------------ destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H24.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e C) as H94.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H94.
------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------- exact H25.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H95.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H95.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C D E).
---------------------------------------------------------------------------intro H96.
apply (@euclidean__tactics.Col__nCol__False C D E H96).
----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 e C D E H91 H92 H94).


------------------------------------------------------------------------- exact H95.
---- exact H9.
Qed.
