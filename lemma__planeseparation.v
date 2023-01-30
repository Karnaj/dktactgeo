Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__3__7a.
Require Export lemma__3__7b.
Require Export lemma__9__5a.
Require Export lemma__9__5b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__outerconnectivity.
Require Export lemma__twolines2.
Require Export logic.
Require Export proposition__10.
Definition lemma__planeseparation : forall A B C D E, (euclidean__defs.OS C D A B) -> ((euclidean__axioms.TS D A B E) -> (euclidean__axioms.TS C A B E)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (exists G H1 Q, (euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A B H1) /\ ((euclidean__axioms.BetS C G Q) /\ ((euclidean__axioms.BetS D H1 Q) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H1.
- assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as H1 by exact H.
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS C U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))))) as __TmpHyp by exact H1.
destruct __TmpHyp as [x H2].
destruct H2 as [x0 H3].
destruct H3 as [x1 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exists x0.
exists x1.
exists x.
split.
-- exact H5.
-- split.
--- exact H7.
--- split.
---- exact H9.
---- split.
----- exact H11.
----- split.
------ exact H13.
------ exact H14.
- destruct H1 as [G H2].
destruct H2 as [H3 H4].
destruct H4 as [Q H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
assert (* Cut *) (~(A = B)) as H16.
-- intro H16.
assert (* Cut *) (euclidean__axioms.Col A B C) as H17.
--- left.
exact H16.
--- apply (@euclidean__tactics.Col__nCol__False A B D H15).
----apply (@euclidean__tactics.not__nCol__Col A B D).
-----intro H18.
apply (@euclidean__tactics.Col__nCol__False A B C H14 H17).


-- assert (* Cut *) (euclidean__axioms.neq B A) as H17.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H16).
--- assert (exists W, (euclidean__axioms.BetS D W E) /\ ((euclidean__axioms.Col A B W) /\ (euclidean__axioms.nCol A B D))) as H18 by exact H0.
destruct H18 as [W H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
assert (* Cut *) (euclidean__axioms.neq C G) as H24.
---- assert (* Cut *) ((euclidean__axioms.neq G Q) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C Q))) as H24.
----- apply (@lemma__betweennotequal.lemma__betweennotequal C G Q H10).
----- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
---- assert (* Cut *) (euclidean__axioms.neq G C) as H25.
----- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C G H24).
----- assert (* Cut *) (euclidean__axioms.neq G Q) as H26.
------ assert (* Cut *) ((euclidean__axioms.neq G Q) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C Q))) as H26.
------- apply (@lemma__betweennotequal.lemma__betweennotequal C G Q H10).
------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H27.
------ assert (* Cut *) (euclidean__axioms.TS C A B E) as H27.
------- assert (* Cut *) ((euclidean__axioms.Col C Q D) \/ (euclidean__axioms.nCol C Q D)) as H27.
-------- apply (@euclidean__tactics.Col__or__nCol C Q D).
-------- assert ((euclidean__axioms.Col C Q D) \/ (euclidean__axioms.nCol C Q D)) as H28 by exact H27.
assert ((euclidean__axioms.Col C Q D) \/ (euclidean__axioms.nCol C Q D)) as __TmpHyp by exact H28.
destruct __TmpHyp as [H29|H29].
--------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H30.
---------- intro H30.
assert (* Cut *) (euclidean__axioms.Col Q C D) as H31.
----------- assert (* Cut *) ((euclidean__axioms.Col Q C D) /\ ((euclidean__axioms.Col Q D C) /\ ((euclidean__axioms.Col D C Q) /\ ((euclidean__axioms.Col C D Q) /\ (euclidean__axioms.Col D Q C))))) as H31.
------------ apply (@lemma__collinearorder.lemma__collinearorder C Q D H29).
------------ destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H32.
----------- assert (* Cut *) (~(euclidean__axioms.neq G H3)) as H32.
------------ intro H32.
assert (* Cut *) (euclidean__axioms.neq D Q) as H33.
------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H33.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
-------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H37.
------------- assert (* Cut *) (euclidean__axioms.Col C G Q) as H34.
-------------- right.
right.
right.
right.
left.
exact H10.
-------------- assert (* Cut *) (euclidean__axioms.Col D H3 Q) as H35.
--------------- right.
right.
right.
right.
left.
exact H12.
--------------- assert (* Cut *) (euclidean__axioms.Col Q C G) as H36.
---------------- assert (* Cut *) ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col G Q C) /\ ((euclidean__axioms.Col Q C G) /\ ((euclidean__axioms.Col C Q G) /\ (euclidean__axioms.Col Q G C))))) as H36.
----------------- apply (@lemma__collinearorder.lemma__collinearorder C G Q H34).
----------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H41.
---------------- assert (* Cut *) (euclidean__axioms.neq C Q) as H37.
----------------- assert (* Cut *) ((euclidean__axioms.neq G Q) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C Q))) as H37.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C G Q H10).
------------------ destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H41.
----------------- assert (* Cut *) (euclidean__axioms.neq Q C) as H38.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C Q H37).
------------------ assert (* Cut *) (euclidean__axioms.Col C G D) as H39.
------------------- apply (@euclidean__tactics.not__nCol__Col C G D).
--------------------intro H39.
apply (@euclidean__tactics.Col__nCol__False C G D H39).
---------------------apply (@lemma__collinear4.lemma__collinear4 Q C G D H36 H31 H38).


------------------- assert (* Cut *) (euclidean__axioms.Col D Q H3) as H40.
-------------------- assert (* Cut *) ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col H3 Q D) /\ ((euclidean__axioms.Col Q D H3) /\ ((euclidean__axioms.Col D Q H3) /\ (euclidean__axioms.Col Q H3 D))))) as H40.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder D H3 Q H35).
--------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H47.
-------------------- assert (* Cut *) (euclidean__axioms.Col D Q C) as H41.
--------------------- assert (* Cut *) ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))))) as H41.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder Q C D H31).
---------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
--------------------- assert (* Cut *) (euclidean__axioms.Col Q H3 C) as H42.
---------------------- apply (@euclidean__tactics.not__nCol__Col Q H3 C).
-----------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False Q H3 C H42).
------------------------apply (@lemma__collinear4.lemma__collinear4 D Q H3 C H40 H41 H33).


---------------------- assert (* Cut *) (euclidean__axioms.Col Q C H3) as H43.
----------------------- assert (* Cut *) ((euclidean__axioms.Col H3 Q C) /\ ((euclidean__axioms.Col H3 C Q) /\ ((euclidean__axioms.Col C Q H3) /\ ((euclidean__axioms.Col Q C H3) /\ (euclidean__axioms.Col C H3 Q))))) as H43.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder Q H3 C H42).
------------------------ destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H50.
----------------------- assert (* Cut *) (~(euclidean__axioms.Col C A B)) as H44.
------------------------ intro H44.
assert (* Cut *) (euclidean__axioms.Col A B C) as H45.
------------------------- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H45.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder C A B H44).
-------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H48.
------------------------- apply (@euclidean__tactics.Col__nCol__False A B D H23).
--------------------------apply (@euclidean__tactics.not__nCol__Col A B D).
---------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False A B C H14 H45).


------------------------ assert (* Cut *) (~((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col D A B))) as H45.
------------------------- intro H45.
destruct H14 as [H46 H47].
destruct H15 as [H48 H49].
destruct H23 as [H50 H51].
destruct H45 as [H52 H53].
destruct H47 as [H54 H55].
destruct H49 as [H56 H57].
destruct H51 as [H58 H59].
destruct H55 as [H60 H61].
destruct H57 as [H62 H63].
destruct H59 as [H64 H65].
destruct H61 as [H66 H67].
destruct H63 as [H68 H69].
destruct H65 as [H70 H71].
destruct H67 as [H72 H73].
destruct H69 as [H74 H75].
destruct H71 as [H76 H77].
assert (* Cut *) (False) as H78.
-------------------------- apply (@H44 H52).
-------------------------- contradiction H78.
------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H46.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H46.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B G H6).
--------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H51.
-------------------------- assert (* Cut *) (euclidean__axioms.Col H3 A B) as H47.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col B A H3) /\ ((euclidean__axioms.Col B H3 A) /\ ((euclidean__axioms.Col H3 A B) /\ ((euclidean__axioms.Col A H3 B) /\ (euclidean__axioms.Col H3 B A))))) as H47.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B H3 H8).
---------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H52.
--------------------------- assert (* Cut *) (euclidean__axioms.Col G C D) as H48.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H48.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G D H39).
----------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
---------------------------- assert (* Cut *) (euclidean__axioms.Col Q D H3) as H49.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col Q D H3) /\ ((euclidean__axioms.Col Q H3 D) /\ ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col D H3 Q) /\ (euclidean__axioms.Col H3 Q D))))) as H49.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D Q H3 H40).
------------------------------ destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H50.
----------------------------- assert (* Cut *) (euclidean__axioms.Col Q D C) as H50.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col Q D C) /\ ((euclidean__axioms.Col Q C D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D C Q) /\ (euclidean__axioms.Col C Q D))))) as H50.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D Q C H41).
------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H51.
------------------------------ assert (* Cut *) (euclidean__axioms.neq D Q) as H51.
------------------------------- assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H51.
-------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
-------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H33.
------------------------------- assert (* Cut *) (euclidean__axioms.neq Q D) as H52.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D Q H51).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col D C H3) as H53.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col D C H3).
----------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False D C H3 H53).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 Q D C H3 H50 H49 H52).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 C D) as H54.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D H3) /\ ((euclidean__axioms.Col C H3 D) /\ ((euclidean__axioms.Col H3 D C) /\ ((euclidean__axioms.Col D H3 C) /\ (euclidean__axioms.Col H3 C D))))) as H54.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C H3 H53).
----------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H62.
---------------------------------- assert (* Cut *) (~(C = D)) as H55.
----------------------------------- intro H55.
assert (* Cut *) (euclidean__axioms.TS C A B E) as H56.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point D (fun C0 => (euclidean__defs.OS C0 D A B) -> ((euclidean__axioms.BetS C0 G Q) -> ((euclidean__axioms.nCol A B C0) -> ((euclidean__axioms.neq C0 G) -> ((euclidean__axioms.neq G C0) -> ((euclidean__axioms.Col C0 Q D) -> ((~(euclidean__axioms.TS C0 A B E)) -> ((euclidean__axioms.Col Q C0 D) -> ((euclidean__axioms.Col C0 G Q) -> ((euclidean__axioms.Col Q C0 G) -> ((euclidean__axioms.neq C0 Q) -> ((euclidean__axioms.neq Q C0) -> ((euclidean__axioms.Col C0 G D) -> ((euclidean__axioms.Col D Q C0) -> ((euclidean__axioms.Col Q H3 C0) -> ((euclidean__axioms.Col Q C0 H3) -> ((~(euclidean__axioms.Col C0 A B)) -> ((~((euclidean__axioms.Col C0 A B) /\ (euclidean__axioms.Col D A B))) -> ((euclidean__axioms.Col G C0 D) -> ((euclidean__axioms.Col Q D C0) -> ((euclidean__axioms.Col D C0 H3) -> ((euclidean__axioms.Col H3 C0 D) -> (euclidean__axioms.TS C0 A B E)))))))))))))))))))))))) with (x := C).
-------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
exact H0.

------------------------------------- exact H55.
------------------------------------- exact H.
------------------------------------- exact H10.
------------------------------------- exact H14.
------------------------------------- exact H24.
------------------------------------- exact H25.
------------------------------------- exact H29.
------------------------------------- exact H30.
------------------------------------- exact H31.
------------------------------------- exact H34.
------------------------------------- exact H36.
------------------------------------- exact H37.
------------------------------------- exact H38.
------------------------------------- exact H39.
------------------------------------- exact H41.
------------------------------------- exact H42.
------------------------------------- exact H43.
------------------------------------- exact H44.
------------------------------------- exact H45.
------------------------------------- exact H48.
------------------------------------- exact H50.
------------------------------------- exact H53.
------------------------------------- exact H54.
------------------------------------ apply (@H30 H56).
----------------------------------- assert (* Cut *) (G = H3) as H56.
------------------------------------ apply (@lemma__twolines2.lemma__twolines2 C D C D G H3 H55 H55 H48 H48 H54 H54).
-------------------------------------intro H56.
apply (@H32).
--------------------------------------apply (@lemma__twolines2.lemma__twolines2 C D A B G H3 H55 H16 H48 H46 H54 H47 H45).


------------------------------------ apply (@H32 H56).
------------ assert (* Cut *) (euclidean__axioms.BetS Q G C) as H33.
------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C G Q H10).
------------- assert (* Cut *) (euclidean__axioms.BetS Q H3 D) as H34.
-------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D H3 Q H12).
-------------- assert (* Cut *) (euclidean__axioms.BetS Q G D) as H35.
--------------- apply (@eq__ind__r euclidean__axioms.Point H3 (fun X => euclidean__axioms.BetS Q X D)) with (x := G).
---------------- exact H34.
----------------apply (@euclidean__tactics.NNPP (G = H3) H32).

--------------- assert (* Cut *) (~(euclidean__axioms.nCol E D G)) as H36.
---------------- intro H36.
assert (* Cut *) (~(euclidean__axioms.nCol E C G)) as H37.
----------------- intro H37.
assert (* Cut *) (~(euclidean__axioms.BetS G C D)) as H38.
------------------ intro H38.
assert (* Cut *) (euclidean__axioms.TS C A B E) as H39.
------------------- apply (@lemma__9__5b.lemma__9__5b A B E D C G H0 H38 H36 H6).
------------------- apply (@H30 H39).
------------------ assert (* Cut *) (~(euclidean__axioms.BetS G D C)) as H39.
------------------- intro H39.
assert (* Cut *) (~(euclidean__axioms.Col G C E)) as H40.
-------------------- intro H40.
assert (* Cut *) (euclidean__axioms.Col E C G) as H41.
--------------------- assert (* Cut *) ((euclidean__axioms.Col C G E) /\ ((euclidean__axioms.Col C E G) /\ ((euclidean__axioms.Col E G C) /\ ((euclidean__axioms.Col G E C) /\ (euclidean__axioms.Col E C G))))) as H41.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder G C E H40).
---------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
--------------------- apply (@euclidean__tactics.Col__nCol__False E C G H37 H41).
-------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H41.
--------------------- apply (@lemma__9__5a.lemma__9__5a A B E D C G H0 H39).
----------------------apply (@euclidean__tactics.nCol__notCol G C E H40).

---------------------- exact H6.
--------------------- apply (@H30 H41).
------------------- assert (* Cut *) (C = D) as H40.
-------------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity Q G C D H33 H35 H38 H39).
-------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H41.
--------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun C0 => (euclidean__defs.OS C0 D A B) -> ((euclidean__axioms.BetS C0 G Q) -> ((euclidean__axioms.nCol A B C0) -> ((euclidean__axioms.neq C0 G) -> ((euclidean__axioms.neq G C0) -> ((euclidean__axioms.Col C0 Q D) -> ((~(euclidean__axioms.TS C0 A B E)) -> ((euclidean__axioms.Col Q C0 D) -> ((euclidean__axioms.BetS Q G C0) -> ((euclidean__axioms.nCol E C0 G) -> ((~(euclidean__axioms.BetS G C0 D)) -> ((~(euclidean__axioms.BetS G D C0)) -> (euclidean__axioms.TS C0 A B E)))))))))))))) with (x := C).
----------------------intro H41.
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
exact H0.

---------------------- exact H40.
---------------------- exact H.
---------------------- exact H10.
---------------------- exact H14.
---------------------- exact H24.
---------------------- exact H25.
---------------------- exact H29.
---------------------- exact H30.
---------------------- exact H31.
---------------------- exact H33.
---------------------- exact H37.
---------------------- exact H38.
---------------------- exact H39.
--------------------- apply (@H30 H41).
----------------- assert (* Cut *) (euclidean__axioms.Col C G E) as H38.
------------------ assert (* Cut *) (euclidean__axioms.Col E C G) as H38.
------------------- apply (@euclidean__tactics.not__nCol__Col E C G H37).
------------------- assert (* Cut *) ((euclidean__axioms.Col C E G) /\ ((euclidean__axioms.Col C G E) /\ ((euclidean__axioms.Col G E C) /\ ((euclidean__axioms.Col E G C) /\ (euclidean__axioms.Col G C E))))) as H39.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder E C G H38).
-------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H42.
------------------ assert (* Cut *) (euclidean__axioms.Col Q G D) as H39.
------------------- right.
right.
right.
right.
left.
exact H35.
------------------- assert (* Cut *) (euclidean__axioms.Col Q G C) as H40.
-------------------- right.
right.
right.
right.
left.
exact H33.
-------------------- assert (* Cut *) (euclidean__axioms.neq Q G) as H41.
--------------------- assert (* Cut *) (euclidean__axioms.Col E C G) as H41.
---------------------- apply (@euclidean__tactics.not__nCol__Col E C G H37).
---------------------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q D))) as H42.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G D H35).
----------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H45.
--------------------- assert (* Cut *) (euclidean__axioms.Col G D C) as H42.
---------------------- apply (@euclidean__tactics.not__nCol__Col G D C).
-----------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False G D C H42).
------------------------apply (@lemma__collinear4.lemma__collinear4 Q G D C H39 H40 H41).


---------------------- assert (* Cut *) (euclidean__axioms.Col C G D) as H43.
----------------------- assert (* Cut *) (euclidean__axioms.Col E C G) as H43.
------------------------ apply (@euclidean__tactics.not__nCol__Col E C G H37).
------------------------ assert (* Cut *) ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G C D) /\ (euclidean__axioms.Col C D G))))) as H44.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder G D C H42).
------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
----------------------- assert (* Cut *) (euclidean__axioms.Col C G E) as H44.
------------------------ assert (* Cut *) (euclidean__axioms.Col E C G) as H44.
------------------------- apply (@euclidean__tactics.not__nCol__Col E C G H37).
------------------------- assert (* Cut *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H45.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G D H43).
-------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H38.
------------------------ assert (* Cut *) (euclidean__axioms.neq G C) as H45.
------------------------- assert (* Cut *) (euclidean__axioms.Col E C G) as H45.
-------------------------- apply (@euclidean__tactics.not__nCol__Col E C G H37).
-------------------------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q D))) as H46.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G D H35).
--------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H25.
------------------------- assert (euclidean__axioms.neq C G) as H46 by exact H24.
assert (* Cut *) (euclidean__axioms.Col G D E) as H47.
-------------------------- apply (@euclidean__tactics.not__nCol__Col G D E).
---------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False G D E H47).
----------------------------apply (@lemma__collinear4.lemma__collinear4 C G D E H43 H44 H46).


-------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H48.
--------------------------- assert (* Cut *) (euclidean__axioms.Col E C G) as H48.
---------------------------- apply (@euclidean__tactics.not__nCol__Col E C G H37).
---------------------------- assert (* Cut *) ((euclidean__axioms.Col D G E) /\ ((euclidean__axioms.Col D E G) /\ ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col G E D) /\ (euclidean__axioms.Col E D G))))) as H49.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder G D E H47).
----------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H57.
--------------------------- apply (@H37).
----------------------------apply (@euclidean__tactics.nCol__notCol E C G).
-----------------------------intro H49.
apply (@euclidean__tactics.Col__nCol__False E D G H36 H48).


---------------- assert (* Cut *) (euclidean__axioms.Col D G E) as H37.
----------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H37.
------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------ assert (* Cut *) ((euclidean__axioms.Col D E G) /\ ((euclidean__axioms.Col D G E) /\ ((euclidean__axioms.Col G E D) /\ ((euclidean__axioms.Col E G D) /\ (euclidean__axioms.Col G D E))))) as H38.
------------------- apply (@lemma__collinearorder.lemma__collinearorder E D G H37).
------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H41.
----------------- assert (* Cut *) (euclidean__axioms.Col D H3 Q) as H38.
------------------ right.
right.
right.
right.
left.
exact H12.
------------------ assert (* Cut *) (euclidean__axioms.Col D G Q) as H39.
------------------- apply (@eq__ind__r euclidean__axioms.Point H3 (fun X => euclidean__axioms.Col D X Q)) with (x := G).
-------------------- exact H38.
--------------------apply (@euclidean__tactics.NNPP (G = H3) H32).

------------------- assert (* Cut *) (euclidean__axioms.neq G D) as H40.
-------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H40.
--------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
--------------------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q D))) as H41.
---------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G D H35).
---------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
-------------------- assert (* Cut *) (euclidean__axioms.neq D G) as H41.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G D H40).
--------------------- assert (* Cut *) (euclidean__axioms.Col G E Q) as H42.
---------------------- apply (@euclidean__tactics.not__nCol__Col G E Q).
-----------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False G E Q H42).
------------------------apply (@lemma__collinear4.lemma__collinear4 D G E Q H37 H39 H41).


---------------------- assert (* Cut *) (euclidean__axioms.Col G E D) as H43.
----------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H43.
------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------ assert (* Cut *) ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col G E D) /\ ((euclidean__axioms.Col E D G) /\ ((euclidean__axioms.Col D E G) /\ (euclidean__axioms.Col E G D))))) as H44.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder D G E H37).
------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H47.
----------------------- assert (* Cut *) (euclidean__axioms.Col D W E) as H44.
------------------------ right.
right.
right.
right.
left.
exact H20.
------------------------ assert (* Cut *) (euclidean__axioms.Col D E W) as H45.
------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H45.
-------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
-------------------------- assert (* Cut *) ((euclidean__axioms.Col W D E) /\ ((euclidean__axioms.Col W E D) /\ ((euclidean__axioms.Col E D W) /\ ((euclidean__axioms.Col D E W) /\ (euclidean__axioms.Col E W D))))) as H46.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder D W E H44).
--------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H53.
------------------------- assert (* Cut *) (euclidean__axioms.Col D E G) as H46.
-------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H46.
--------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
--------------------------- assert (* Cut *) ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col E D G) /\ ((euclidean__axioms.Col D G E) /\ ((euclidean__axioms.Col G D E) /\ (euclidean__axioms.Col D E G))))) as H47.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder G E D H43).
---------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
-------------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H47.
--------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H47.
---------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------- assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H48.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
----------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
--------------------------- assert (* Cut *) (euclidean__axioms.Col E W G) as H48.
---------------------------- apply (@euclidean__tactics.not__nCol__Col E W G).
-----------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False E W G H48).
------------------------------apply (@lemma__collinear4.lemma__collinear4 D E W G H45 H46 H47).


---------------------------- assert (* Cut *) (euclidean__axioms.Col E W D) as H49.
----------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H49.
------------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------ assert (* Cut *) ((euclidean__axioms.Col E D W) /\ ((euclidean__axioms.Col E W D) /\ ((euclidean__axioms.Col W D E) /\ ((euclidean__axioms.Col D W E) /\ (euclidean__axioms.Col W E D))))) as H50.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D E W H45).
------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H53.
----------------------------- assert (* Cut *) (euclidean__axioms.neq W E) as H50.
------------------------------ assert (* Cut *) (euclidean__axioms.Col E D G) as H50.
------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------- assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H51.
-------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
-------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H52.
------------------------------ assert (* Cut *) (euclidean__axioms.neq E W) as H51.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric W E H50).
------------------------------- assert (* Cut *) (euclidean__axioms.Col W G D) as H52.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col W G D).
---------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False W G D H52).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 E W G D H48 H49 H51).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col B W G) as H53.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col B W G).
----------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False B W G H53).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 A B W G H22 H6 H16).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col W G B) as H54.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H54.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col W B G) /\ ((euclidean__axioms.Col W G B) /\ ((euclidean__axioms.Col G B W) /\ ((euclidean__axioms.Col B G W) /\ (euclidean__axioms.Col G W B))))) as H55.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B W G H53).
------------------------------------ destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H58.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B A W) as H55.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H55.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A W) /\ ((euclidean__axioms.Col B W A) /\ ((euclidean__axioms.Col W A B) /\ ((euclidean__axioms.Col A W B) /\ (euclidean__axioms.Col W B A))))) as H56.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B W H22).
------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H57.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B A G) as H56.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col E D G) as H56.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H57.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B G H6).
-------------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H58.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col A W G) as H57.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col A W G).
--------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False A W G H57).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 B A W G H55 H56 H17).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col W G A) as H58.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H58.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col W A G) /\ ((euclidean__axioms.Col W G A) /\ ((euclidean__axioms.Col G A W) /\ ((euclidean__axioms.Col A G W) /\ (euclidean__axioms.Col G W A))))) as H59.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A W G H57).
---------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
-------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq W G)) as H59.
--------------------------------------- intro H59.
assert (* Cut *) (euclidean__axioms.Col G D B) as H60.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col G D B).
-----------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False G D B H60).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 W G D B H52 H54 H59).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B D) as H61.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H61.
------------------------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D G B) /\ ((euclidean__axioms.Col D B G) /\ ((euclidean__axioms.Col B G D) /\ ((euclidean__axioms.Col G B D) /\ (euclidean__axioms.Col B D G))))) as H62.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G D B H60).
------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H69.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H62.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E D G) as H62.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H63.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A G H56).
-------------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H68.
------------------------------------------ assert (* Cut *) (~(euclidean__axioms.neq G B)) as H63.
------------------------------------------- intro H63.
assert (* Cut *) (euclidean__axioms.Col B D A) as H64.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col B D A).
---------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False B D A H64).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G B D A H61 H62 H63).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B D) as H65.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H65.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B))))) as H66.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B D A H64).
----------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H71.
--------------------------------------------- apply (@H36).
----------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
-----------------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False A B D H23 H65).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D A) as H64.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col G D A).
---------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False G D A H64).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 W G D A H52 H58 H59).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A D) as H65.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H65.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D G A) /\ ((euclidean__axioms.Col D A G) /\ ((euclidean__axioms.Col A G D) /\ ((euclidean__axioms.Col G A D) /\ (euclidean__axioms.Col A D G))))) as H66.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G D A H64).
----------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H66.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H66.
----------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H67.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G B A H62).
------------------------------------------------ destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H74.
---------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq G A)) as H67.
----------------------------------------------- intro H67.
assert (* Cut *) (euclidean__axioms.Col A D B) as H68.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col A D B).
-------------------------------------------------intro H68.
apply (@euclidean__tactics.Col__nCol__False A D B H68).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G A D B H65 H66 H67).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B D) as H69.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H69.
-------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H70.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A D B H68).
--------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H77.
------------------------------------------------- apply (@H36).
--------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
---------------------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False A B D H23 H69).


----------------------------------------------- assert (* Cut *) (A = G) as H68.
------------------------------------------------ assert (* Cut *) (G = A) as H68.
------------------------------------------------- apply (@euclidean__tactics.NNPP (G = A) H67).
------------------------------------------------- assert (* Cut *) (G = B) as H69.
-------------------------------------------------- apply (@euclidean__tactics.NNPP (G = B) H63).
-------------------------------------------------- assert (* Cut *) (G = H3) as H70.
--------------------------------------------------- apply (@euclidean__tactics.NNPP (G = H3) H32).
--------------------------------------------------- apply (@logic.eq__sym Point G A H68).
------------------------------------------------ assert (* Cut *) (B = G) as H69.
------------------------------------------------- assert (* Cut *) (G = A) as H69.
-------------------------------------------------- apply (@euclidean__tactics.NNPP (G = A) H67).
-------------------------------------------------- assert (* Cut *) (G = B) as H70.
--------------------------------------------------- apply (@euclidean__tactics.NNPP (G = B) H63).
--------------------------------------------------- assert (* Cut *) (G = H3) as H71.
---------------------------------------------------- apply (@euclidean__tactics.NNPP (G = H3) H32).
---------------------------------------------------- apply (@logic.eq__sym Point G B H70).
------------------------------------------------- assert (* Cut *) (A = B) as H70.
-------------------------------------------------- assert (* Cut *) (G = A) as H70.
--------------------------------------------------- apply (@euclidean__tactics.NNPP (G = A) H67).
--------------------------------------------------- assert (* Cut *) (G = B) as H71.
---------------------------------------------------- apply (@euclidean__tactics.NNPP (G = B) H63).
---------------------------------------------------- assert (* Cut *) (G = H3) as H72.
----------------------------------------------------- apply (@euclidean__tactics.NNPP (G = H3) H32).
----------------------------------------------------- apply (@logic.eq__trans Point A G B H68).
------------------------------------------------------apply (@logic.eq__sym Point B G H69).

-------------------------------------------------- apply (@H16 H70).
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D G E) as H60.
---------------------------------------- apply (@eq__ind euclidean__axioms.Point W (fun X => euclidean__axioms.BetS D X E)) with (y := G).
----------------------------------------- exact H20.
-----------------------------------------apply (@euclidean__tactics.NNPP (W = G) H59).

---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H61.
----------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D G E H60).
----------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS G D C)) as H62.
------------------------------------------ intro H62.
assert (* Cut *) (euclidean__axioms.BetS E G C) as H63.
------------------------------------------- apply (@lemma__3__7b.lemma__3__7b E G D C H61 H62).
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C G E) as H64.
-------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E G C H63).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H65.
--------------------------------------------- exists G.
split.
---------------------------------------------- exact H64.
---------------------------------------------- split.
----------------------------------------------- exact H6.
----------------------------------------------- exact H14.
--------------------------------------------- apply (@H30 H65).
------------------------------------------ assert (* Cut *) (~(euclidean__axioms.BetS G C D)) as H63.
------------------------------------------- intro H63.
assert (* Cut *) (euclidean__axioms.BetS E G C) as H64.
-------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity E G C D H61 H63).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C G E) as H65.
--------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E G C H64).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H66.
---------------------------------------------- exists G.
split.
----------------------------------------------- exact H65.
----------------------------------------------- split.
------------------------------------------------ exact H6.
------------------------------------------------ exact H14.
---------------------------------------------- apply (@H30 H66).
------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS C G D)) as H64.
-------------------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.BetS D G Q) as H65.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H3 (fun X => euclidean__axioms.BetS D X Q)) with (x := G).
---------------------------------------------- exact H12.
----------------------------------------------apply (@euclidean__tactics.NNPP (G = H3) H32).

--------------------------------------------- assert (euclidean__axioms.BetS Q G C) as H66 by exact H33.
assert (* Cut *) (euclidean__axioms.BetS D G C) as H67.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C G D H64).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G D) as H68.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H68.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq D G) /\ (euclidean__axioms.neq D C))) as H69.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D G C H67).
------------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H40.
----------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS G D C)) as H69.
------------------------------------------------ intro H69.
assert (* Cut *) (euclidean__axioms.BetS C D G) as H70.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G D C H69).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C G C) as H71.
-------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a C D G C H70 H67).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C C) as H72.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H72.
---------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C C))) as H73.
----------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C G C H71).
----------------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H77.
--------------------------------------------------- assert (* Cut *) (C = C) as H73.
---------------------------------------------------- assert (* Cut *) (False) as H73.
----------------------------------------------------- apply (@H62 H69).
----------------------------------------------------- assert (* Cut *) (False) as H74.
------------------------------------------------------ assert (* Cut *) (C = C) as H74.
------------------------------------------------------- apply (@logic.eq__refl Point C).
------------------------------------------------------- apply (@H72 H74).
------------------------------------------------------ assert (False) as H75 by exact H74.
apply (@logic.eq__refl Point C).
---------------------------------------------------- apply (@H36).
-----------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
------------------------------------------------------intro H74.
apply (@H62 H69).


------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.BetS G C D)) as H70.
------------------------------------------------- intro H70.
assert (euclidean__axioms.BetS D G C) as H71 by exact H67.
assert (* Cut *) (euclidean__axioms.BetS C G C) as H72.
-------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity C G C D H64 H70).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C C) as H73.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H73.
---------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C C))) as H74.
----------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C G C H72).
----------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
--------------------------------------------------- assert (* Cut *) (C = C) as H74.
---------------------------------------------------- assert (* Cut *) (False) as H74.
----------------------------------------------------- apply (@H63 H70).
----------------------------------------------------- assert (* Cut *) (False) as H75.
------------------------------------------------------ assert (* Cut *) (C = C) as H75.
------------------------------------------------------- apply (@logic.eq__refl Point C).
------------------------------------------------------- apply (@H73 H75).
------------------------------------------------------ assert (False) as H76 by exact H75.
apply (@logic.eq__refl Point C).
---------------------------------------------------- apply (@H36).
-----------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
------------------------------------------------------intro H75.
apply (@H63 H70).


------------------------------------------------- assert (euclidean__axioms.BetS Q G D) as H71 by exact H35.
assert (euclidean__axioms.BetS Q G C) as H72 by exact H66.
assert (* Cut *) (C = D) as H73.
-------------------------------------------------- apply (@lemma__outerconnectivity.lemma__outerconnectivity Q G C D H72 H71 H70 H69).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H74.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun C0 => (euclidean__defs.OS C0 D A B) -> ((euclidean__axioms.BetS C0 G Q) -> ((euclidean__axioms.nCol A B C0) -> ((euclidean__axioms.neq C0 G) -> ((euclidean__axioms.neq G C0) -> ((euclidean__axioms.Col C0 Q D) -> ((~(euclidean__axioms.TS C0 A B E)) -> ((euclidean__axioms.Col Q C0 D) -> ((euclidean__axioms.BetS Q G C0) -> ((~(euclidean__axioms.BetS G D C0)) -> ((~(euclidean__axioms.BetS G C0 D)) -> ((euclidean__axioms.BetS C0 G D) -> ((euclidean__axioms.BetS Q G C0) -> ((euclidean__axioms.BetS D G C0) -> ((~(euclidean__axioms.BetS G D C0)) -> ((~(euclidean__axioms.BetS G C0 D)) -> ((euclidean__axioms.BetS Q G C0) -> (euclidean__axioms.TS C0 A B E))))))))))))))))))) with (x := C).
----------------------------------------------------intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
exact H0.

---------------------------------------------------- exact H73.
---------------------------------------------------- exact H.
---------------------------------------------------- exact H10.
---------------------------------------------------- exact H14.
---------------------------------------------------- exact H24.
---------------------------------------------------- exact H25.
---------------------------------------------------- exact H29.
---------------------------------------------------- exact H30.
---------------------------------------------------- exact H31.
---------------------------------------------------- exact H33.
---------------------------------------------------- exact H62.
---------------------------------------------------- exact H63.
---------------------------------------------------- exact H64.
---------------------------------------------------- exact H66.
---------------------------------------------------- exact H67.
---------------------------------------------------- exact H69.
---------------------------------------------------- exact H70.
---------------------------------------------------- exact H72.
--------------------------------------------------- apply (@H30 H74).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C D) as H65.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H65.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G W A) /\ ((euclidean__axioms.Col G A W) /\ ((euclidean__axioms.Col A W G) /\ ((euclidean__axioms.Col W A G) /\ (euclidean__axioms.Col A G W))))) as H66.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder W G A H58).
----------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H31.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q G C) as H66.
---------------------------------------------- right.
right.
right.
right.
left.
exact H33.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C G) as H67.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H67.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G Q C) /\ ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col C Q G) /\ ((euclidean__axioms.Col Q C G) /\ (euclidean__axioms.Col C G Q))))) as H68.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q G C H66).
------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H75.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q C) as H68.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E D G) as H68.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q C))) as H69.
-------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G C H33).
-------------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H73.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D G) as H69.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C D G).
--------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False C D G H69).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 Q C D G H65 H67 H68).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C D) as H70.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H70.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D G H36).
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H71.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D G H69).
---------------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H76.
-------------------------------------------------- assert ((G = C) \/ ((G = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C G D) \/ ((euclidean__axioms.BetS G C D) \/ (euclidean__axioms.BetS G D C)))))) as H71 by exact H70.
assert (* Cut *) (euclidean__axioms.TS C A B E) as H72.
--------------------------------------------------- assert ((G = C) \/ ((G = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C G D) \/ ((euclidean__axioms.BetS G C D) \/ (euclidean__axioms.BetS G D C)))))) as H72 by exact H71.
assert ((G = C) \/ ((G = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C G D) \/ ((euclidean__axioms.BetS G C D) \/ (euclidean__axioms.BetS G D C)))))) as __TmpHyp0 by exact H72.
destruct __TmpHyp0 as [H73|H73].
---------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H74.
----------------------------------------------------- intro H74.
assert (* Cut *) (euclidean__axioms.Col A B C) as H75.
------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun G0 => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.BetS C G0 Q) -> ((euclidean__axioms.neq C G0) -> ((euclidean__axioms.neq G0 C) -> ((euclidean__axioms.neq G0 Q) -> ((~(euclidean__axioms.neq G0 H3)) -> ((euclidean__axioms.BetS Q G0 C) -> ((euclidean__axioms.BetS Q G0 D) -> ((~(euclidean__axioms.nCol E D G0)) -> ((euclidean__axioms.Col D G0 E) -> ((euclidean__axioms.Col D G0 Q) -> ((euclidean__axioms.neq G0 D) -> ((euclidean__axioms.neq D G0) -> ((euclidean__axioms.Col G0 E Q) -> ((euclidean__axioms.Col G0 E D) -> ((euclidean__axioms.Col D E G0) -> ((euclidean__axioms.Col E W G0) -> ((euclidean__axioms.Col W G0 D) -> ((euclidean__axioms.Col B W G0) -> ((euclidean__axioms.Col W G0 B) -> ((euclidean__axioms.Col B A G0) -> ((euclidean__axioms.Col A W G0) -> ((euclidean__axioms.Col W G0 A) -> ((~(euclidean__axioms.neq W G0)) -> ((euclidean__axioms.BetS D G0 E) -> ((euclidean__axioms.BetS E G0 D) -> ((~(euclidean__axioms.BetS G0 D C)) -> ((~(euclidean__axioms.BetS G0 C D)) -> ((~(euclidean__axioms.BetS C G0 D)) -> ((euclidean__axioms.Col Q G0 C) -> ((euclidean__axioms.Col Q C G0) -> ((euclidean__axioms.Col C D G0) -> ((euclidean__axioms.Col G0 C D) -> (euclidean__axioms.Col A B C))))))))))))))))))))))))))))))))))) with (x := G).
-------------------------------------------------------intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
exact H75.

------------------------------------------------------- exact H73.
------------------------------------------------------- exact H6.
------------------------------------------------------- exact H10.
------------------------------------------------------- exact H24.
------------------------------------------------------- exact H25.
------------------------------------------------------- exact H26.
------------------------------------------------------- exact H32.
------------------------------------------------------- exact H33.
------------------------------------------------------- exact H35.
------------------------------------------------------- exact H36.
------------------------------------------------------- exact H37.
------------------------------------------------------- exact H39.
------------------------------------------------------- exact H40.
------------------------------------------------------- exact H41.
------------------------------------------------------- exact H42.
------------------------------------------------------- exact H43.
------------------------------------------------------- exact H46.
------------------------------------------------------- exact H48.
------------------------------------------------------- exact H52.
------------------------------------------------------- exact H53.
------------------------------------------------------- exact H54.
------------------------------------------------------- exact H56.
------------------------------------------------------- exact H57.
------------------------------------------------------- exact H58.
------------------------------------------------------- exact H59.
------------------------------------------------------- exact H60.
------------------------------------------------------- exact H61.
------------------------------------------------------- exact H62.
------------------------------------------------------- exact H63.
------------------------------------------------------- exact H64.
------------------------------------------------------- exact H66.
------------------------------------------------------- exact H67.
------------------------------------------------------- exact H69.
------------------------------------------------------- exact H70.
------------------------------------------------------ apply (@H25 H73).
----------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
------------------------------------------------------intro H75.
destruct H14 as [H76 H77].
destruct H15 as [H78 H79].
destruct H23 as [H80 H81].
destruct H77 as [H82 H83].
destruct H79 as [H84 H85].
destruct H81 as [H86 H87].
destruct H83 as [H88 H89].
destruct H85 as [H90 H91].
destruct H87 as [H92 H93].
destruct H89 as [H94 H95].
destruct H91 as [H96 H97].
destruct H93 as [H98 H99].
destruct H95 as [H100 H101].
destruct H97 as [H102 H103].
destruct H99 as [H104 H105].
assert (* Cut *) (False) as H106.
------------------------------------------------------- apply (@H74 H30).
------------------------------------------------------- assert (* Cut *) (False) as H107.
-------------------------------------------------------- apply (@H25 H73).
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H108.
--------------------------------------------------------- intro H108.
intro H109.
apply (@H36).
----------------------------------------------------------split.
----------------------------------------------------------- exact H108.
----------------------------------------------------------- exact H109.

--------------------------------------------------------- contradiction H107.

---------------------------------------------------- destruct H73 as [H74|H74].
----------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H75.
------------------------------------------------------ intro H75.
assert (* Cut *) (euclidean__axioms.Col A B D) as H76.
------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun G0 => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.BetS C G0 Q) -> ((euclidean__axioms.neq C G0) -> ((euclidean__axioms.neq G0 C) -> ((euclidean__axioms.neq G0 Q) -> ((~(euclidean__axioms.neq G0 H3)) -> ((euclidean__axioms.BetS Q G0 C) -> ((euclidean__axioms.BetS Q G0 D) -> ((~(euclidean__axioms.nCol E D G0)) -> ((euclidean__axioms.Col D G0 E) -> ((euclidean__axioms.Col D G0 Q) -> ((euclidean__axioms.neq G0 D) -> ((euclidean__axioms.neq D G0) -> ((euclidean__axioms.Col G0 E Q) -> ((euclidean__axioms.Col G0 E D) -> ((euclidean__axioms.Col D E G0) -> ((euclidean__axioms.Col E W G0) -> ((euclidean__axioms.Col W G0 D) -> ((euclidean__axioms.Col B W G0) -> ((euclidean__axioms.Col W G0 B) -> ((euclidean__axioms.Col B A G0) -> ((euclidean__axioms.Col A W G0) -> ((euclidean__axioms.Col W G0 A) -> ((~(euclidean__axioms.neq W G0)) -> ((euclidean__axioms.BetS D G0 E) -> ((euclidean__axioms.BetS E G0 D) -> ((~(euclidean__axioms.BetS G0 D C)) -> ((~(euclidean__axioms.BetS G0 C D)) -> ((~(euclidean__axioms.BetS C G0 D)) -> ((euclidean__axioms.Col Q G0 C) -> ((euclidean__axioms.Col Q C G0) -> ((euclidean__axioms.Col C D G0) -> ((euclidean__axioms.Col G0 C D) -> (euclidean__axioms.Col A B D))))))))))))))))))))))))))))))))))) with (x := G).
--------------------------------------------------------intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
exact H76.

-------------------------------------------------------- exact H74.
-------------------------------------------------------- exact H6.
-------------------------------------------------------- exact H10.
-------------------------------------------------------- exact H24.
-------------------------------------------------------- exact H25.
-------------------------------------------------------- exact H26.
-------------------------------------------------------- exact H32.
-------------------------------------------------------- exact H33.
-------------------------------------------------------- exact H35.
-------------------------------------------------------- exact H36.
-------------------------------------------------------- exact H37.
-------------------------------------------------------- exact H39.
-------------------------------------------------------- exact H40.
-------------------------------------------------------- exact H41.
-------------------------------------------------------- exact H42.
-------------------------------------------------------- exact H43.
-------------------------------------------------------- exact H46.
-------------------------------------------------------- exact H48.
-------------------------------------------------------- exact H52.
-------------------------------------------------------- exact H53.
-------------------------------------------------------- exact H54.
-------------------------------------------------------- exact H56.
-------------------------------------------------------- exact H57.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- exact H69.
-------------------------------------------------------- exact H70.
------------------------------------------------------- apply (@H36).
--------------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
---------------------------------------------------------intro H77.
apply (@H40 H74).


------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
-------------------------------------------------------intro H76.
destruct H14 as [H77 H78].
destruct H15 as [H79 H80].
destruct H23 as [H81 H82].
destruct H78 as [H83 H84].
destruct H80 as [H85 H86].
destruct H82 as [H87 H88].
destruct H84 as [H89 H90].
destruct H86 as [H91 H92].
destruct H88 as [H93 H94].
destruct H90 as [H95 H96].
destruct H92 as [H97 H98].
destruct H94 as [H99 H100].
destruct H96 as [H101 H102].
destruct H98 as [H103 H104].
destruct H100 as [H105 H106].
assert (* Cut *) (False) as H107.
-------------------------------------------------------- apply (@H75 H30).
-------------------------------------------------------- assert (* Cut *) (False) as H108.
--------------------------------------------------------- apply (@H40 H74).
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H109.
---------------------------------------------------------- intro H109.
intro H110.
apply (@H36).
-----------------------------------------------------------split.
------------------------------------------------------------ exact H109.
------------------------------------------------------------ exact H110.

---------------------------------------------------------- contradiction H108.

----------------------------------------------------- destruct H74 as [H75|H75].
------------------------------------------------------ assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H76.
------------------------------------------------------- intro H76.
assert (* Cut *) (euclidean__axioms.TS C A B E) as H77.
-------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun C0 => (euclidean__defs.OS C0 D A B) -> ((euclidean__axioms.BetS C0 G Q) -> ((euclidean__axioms.nCol A B C0) -> ((euclidean__axioms.neq C0 G) -> ((euclidean__axioms.neq G C0) -> ((euclidean__axioms.Col C0 Q D) -> ((~(euclidean__axioms.TS C0 A B E)) -> ((euclidean__axioms.Col Q C0 D) -> ((euclidean__axioms.BetS Q G C0) -> ((~(euclidean__axioms.BetS G D C0)) -> ((~(euclidean__axioms.BetS G C0 D)) -> ((~(euclidean__axioms.BetS C0 G D)) -> ((euclidean__axioms.Col Q C0 D) -> ((euclidean__axioms.Col Q G C0) -> ((euclidean__axioms.Col Q C0 G) -> ((euclidean__axioms.neq Q C0) -> ((euclidean__axioms.Col C0 D G) -> ((euclidean__axioms.Col G C0 D) -> ((~(euclidean__axioms.TS C0 A B E)) -> (euclidean__axioms.TS C0 A B E))))))))))))))))))))) with (x := C).
---------------------------------------------------------intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
exact H0.

--------------------------------------------------------- exact H75.
--------------------------------------------------------- exact H.
--------------------------------------------------------- exact H10.
--------------------------------------------------------- exact H14.
--------------------------------------------------------- exact H24.
--------------------------------------------------------- exact H25.
--------------------------------------------------------- exact H29.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- exact H31.
--------------------------------------------------------- exact H33.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- exact H67.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- exact H69.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- exact H76.
-------------------------------------------------------- apply (@H30 H77).
------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
--------------------------------------------------------intro H77.
destruct H14 as [H78 H79].
destruct H15 as [H80 H81].
destruct H23 as [H82 H83].
destruct H79 as [H84 H85].
destruct H81 as [H86 H87].
destruct H83 as [H88 H89].
destruct H85 as [H90 H91].
destruct H87 as [H92 H93].
destruct H89 as [H94 H95].
destruct H91 as [H96 H97].
destruct H93 as [H98 H99].
destruct H95 as [H100 H101].
destruct H97 as [H102 H103].
destruct H99 as [H104 H105].
destruct H101 as [H106 H107].
assert (* Cut *) (False) as H108.
--------------------------------------------------------- apply (@H76 H30).
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H109.
---------------------------------------------------------- intro H109.
intro H110.
apply (@H36).
-----------------------------------------------------------split.
------------------------------------------------------------ exact H109.
------------------------------------------------------------ exact H110.

---------------------------------------------------------- contradiction H108.

------------------------------------------------------ destruct H75 as [H76|H76].
------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H77.
-------------------------------------------------------- intro H77.
apply (@H36).
---------------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
----------------------------------------------------------intro H78.
apply (@H64 H76).


-------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
---------------------------------------------------------intro H78.
destruct H14 as [H79 H80].
destruct H15 as [H81 H82].
destruct H23 as [H83 H84].
destruct H80 as [H85 H86].
destruct H82 as [H87 H88].
destruct H84 as [H89 H90].
destruct H86 as [H91 H92].
destruct H88 as [H93 H94].
destruct H90 as [H95 H96].
destruct H92 as [H97 H98].
destruct H94 as [H99 H100].
destruct H96 as [H101 H102].
destruct H98 as [H103 H104].
destruct H100 as [H105 H106].
destruct H102 as [H107 H108].
assert (* Cut *) (False) as H109.
---------------------------------------------------------- apply (@H77 H30).
---------------------------------------------------------- assert (* Cut *) (False) as H110.
----------------------------------------------------------- apply (@H64 H76).
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H111.
------------------------------------------------------------ intro H111.
intro H112.
apply (@H36).
-------------------------------------------------------------split.
-------------------------------------------------------------- exact H111.
-------------------------------------------------------------- exact H112.

------------------------------------------------------------ contradiction H110.

------------------------------------------------------- destruct H76 as [H77|H77].
-------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H78.
--------------------------------------------------------- intro H78.
apply (@H36).
----------------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
-----------------------------------------------------------intro H79.
apply (@H63 H77).


--------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
----------------------------------------------------------intro H79.
destruct H14 as [H80 H81].
destruct H15 as [H82 H83].
destruct H23 as [H84 H85].
destruct H81 as [H86 H87].
destruct H83 as [H88 H89].
destruct H85 as [H90 H91].
destruct H87 as [H92 H93].
destruct H89 as [H94 H95].
destruct H91 as [H96 H97].
destruct H93 as [H98 H99].
destruct H95 as [H100 H101].
destruct H97 as [H102 H103].
destruct H99 as [H104 H105].
destruct H101 as [H106 H107].
destruct H103 as [H108 H109].
assert (* Cut *) (False) as H110.
----------------------------------------------------------- apply (@H78 H30).
----------------------------------------------------------- assert (* Cut *) (False) as H111.
------------------------------------------------------------ apply (@H63 H77).
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H112.
------------------------------------------------------------- intro H112.
intro H113.
apply (@H36).
--------------------------------------------------------------split.
--------------------------------------------------------------- exact H112.
--------------------------------------------------------------- exact H113.

------------------------------------------------------------- contradiction H111.

-------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H78.
--------------------------------------------------------- intro H78.
apply (@H36).
----------------------------------------------------------apply (@euclidean__tactics.nCol__notCol E D G).
-----------------------------------------------------------intro H79.
apply (@H62 H77).


--------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
----------------------------------------------------------intro H79.
destruct H14 as [H80 H81].
destruct H15 as [H82 H83].
destruct H23 as [H84 H85].
destruct H81 as [H86 H87].
destruct H83 as [H88 H89].
destruct H85 as [H90 H91].
destruct H87 as [H92 H93].
destruct H89 as [H94 H95].
destruct H91 as [H96 H97].
destruct H93 as [H98 H99].
destruct H95 as [H100 H101].
destruct H97 as [H102 H103].
destruct H99 as [H104 H105].
destruct H101 as [H106 H107].
destruct H103 as [H108 H109].
assert (* Cut *) (False) as H110.
----------------------------------------------------------- apply (@H78 H30).
----------------------------------------------------------- assert (* Cut *) (False) as H111.
------------------------------------------------------------ apply (@H62 H77).
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E D) -> (((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq D G) /\ ((~(euclidean__axioms.BetS E D G)) /\ ((~(euclidean__axioms.BetS E G D)) /\ (~(euclidean__axioms.BetS D E G)))))) -> False)) as H112.
------------------------------------------------------------- intro H112.
intro H113.
apply (@H36).
--------------------------------------------------------------split.
--------------------------------------------------------------- exact H112.
--------------------------------------------------------------- exact H113.

------------------------------------------------------------- contradiction H111.

--------------------------------------------------- apply (@H30 H72).
---------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
-----------intro H31.
destruct H14 as [H32 H33].
destruct H15 as [H34 H35].
destruct H23 as [H36 H37].
destruct H33 as [H38 H39].
destruct H35 as [H40 H41].
destruct H37 as [H42 H43].
destruct H39 as [H44 H45].
destruct H41 as [H46 H47].
destruct H43 as [H48 H49].
destruct H45 as [H50 H51].
destruct H47 as [H52 H53].
destruct H49 as [H54 H55].
destruct H51 as [H56 H57].
destruct H53 as [H58 H59].
destruct H55 as [H60 H61].
assert (* Cut *) (False) as H62.
------------ apply (@H30 H31).
------------ contradiction H62.

--------- assert (* Cut *) (~(~(euclidean__axioms.TS C A B E))) as H30.
---------- intro H30.
assert (* Cut *) (~(euclidean__axioms.Col Q C D)) as H31.
----------- intro H31.
assert (* Cut *) (euclidean__axioms.Col C Q D) as H32.
------------ assert (* Cut *) ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))))) as H32.
------------- apply (@lemma__collinearorder.lemma__collinearorder Q C D H31).
------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H33.
------------ apply (@euclidean__tactics.Col__nCol__False C Q D H29 H32).
----------- assert (* Cut *) (exists F, (euclidean__axioms.BetS C F H3) /\ (euclidean__axioms.BetS D F G)) as H32.
------------ apply (@euclidean__axioms.postulate__Pasch__inner C D Q G H3 H10 H12 H29).
------------ destruct H32 as [F H33].
destruct H33 as [H34 H35].
assert (* Cut *) (euclidean__axioms.BetS H3 F C) as H36.
------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C F H3 H34).
------------- assert (* Cut *) (euclidean__axioms.BetS G F D) as H37.
-------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D F G H35).
-------------- assert (* Cut *) (~(euclidean__axioms.Col E D G)) as H38.
--------------- intro H38.
assert (* Cut *) (~(euclidean__axioms.neq W G)) as H39.
---------------- intro H39.
assert (* Cut *) (euclidean__axioms.Col D E G) as H40.
----------------- assert (* Cut *) ((euclidean__axioms.Col D E G) /\ ((euclidean__axioms.Col D G E) /\ ((euclidean__axioms.Col G E D) /\ ((euclidean__axioms.Col E G D) /\ (euclidean__axioms.Col G D E))))) as H40.
------------------ apply (@lemma__collinearorder.lemma__collinearorder E D G H38).
------------------ destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H41.
----------------- assert (* Cut *) (euclidean__axioms.Col D W E) as H41.
------------------ right.
right.
right.
right.
left.
exact H20.
------------------ assert (* Cut *) (euclidean__axioms.Col B G W) as H42.
------------------- apply (@euclidean__tactics.not__nCol__Col B G W).
--------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False B G W H42).
---------------------apply (@lemma__collinear4.lemma__collinear4 A B G W H6 H22 H16).


------------------- assert (* Cut *) (euclidean__axioms.Col W B G) as H43.
-------------------- assert (* Cut *) ((euclidean__axioms.Col G B W) /\ ((euclidean__axioms.Col G W B) /\ ((euclidean__axioms.Col W B G) /\ ((euclidean__axioms.Col B W G) /\ (euclidean__axioms.Col W G B))))) as H43.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder B G W H42).
--------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H48.
-------------------- assert (* Cut *) (euclidean__axioms.Col W B A) as H44.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A W) /\ ((euclidean__axioms.Col B W A) /\ ((euclidean__axioms.Col W A B) /\ ((euclidean__axioms.Col A W B) /\ (euclidean__axioms.Col W B A))))) as H44.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder A B W H22).
---------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
--------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H45.
---------------------- assert (* Cut *) ((W = B) \/ (euclidean__axioms.neq W B)) as H45.
----------------------- apply (@euclidean__tactics.eq__or__neq W B).
----------------------- assert ((W = B) \/ (euclidean__axioms.neq W B)) as H46 by exact H45.
assert ((W = B) \/ (euclidean__axioms.neq W B)) as __TmpHyp0 by exact H46.
destruct __TmpHyp0 as [H47|H47].
------------------------ assert (* Cut *) (euclidean__axioms.Col B A G) as H48.
------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H48.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B G H6).
-------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
------------------------- assert (* Cut *) (euclidean__axioms.Col B A W) as H49.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col B W A) /\ ((euclidean__axioms.Col B A W) /\ ((euclidean__axioms.Col A W B) /\ ((euclidean__axioms.Col W A B) /\ (euclidean__axioms.Col A B W))))) as H49.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder W B A H44).
--------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H52.
-------------------------- assert (* Cut *) (euclidean__axioms.Col A G W) as H50.
--------------------------- apply (@euclidean__tactics.not__nCol__Col A G W).
----------------------------intro H50.
apply (@euclidean__tactics.Col__nCol__False A G W H50).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 B A G W H48 H49 H17).


--------------------------- assert (* Cut *) (euclidean__axioms.Col A G B) as H51.
---------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun W0 => (euclidean__axioms.BetS D W0 E) -> ((euclidean__axioms.Col A B W0) -> ((euclidean__axioms.neq W0 G) -> ((euclidean__axioms.Col D W0 E) -> ((euclidean__axioms.Col B G W0) -> ((euclidean__axioms.Col W0 B G) -> ((euclidean__axioms.Col W0 B A) -> ((euclidean__axioms.Col B A W0) -> ((euclidean__axioms.Col A G W0) -> (euclidean__axioms.Col A G B))))))))))) with (x := W).
-----------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
exact H59.

----------------------------- exact H47.
----------------------------- exact H20.
----------------------------- exact H22.
----------------------------- exact H39.
----------------------------- exact H41.
----------------------------- exact H42.
----------------------------- exact H43.
----------------------------- exact H44.
----------------------------- exact H49.
----------------------------- exact H50.
---------------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H52.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H52.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A G B H51).
------------------------------ destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H60.
----------------------------- exact H52.
------------------------ assert (* Cut *) (euclidean__axioms.Col B G A) as H48.
------------------------- apply (@euclidean__tactics.not__nCol__Col B G A).
--------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False B G A H48).
---------------------------apply (@lemma__collinear4.lemma__collinear4 W B G A H43 H44 H47).


------------------------- exact H48.
---------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H46.
----------------------- assert (* Cut *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H46.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder B G A H45).
------------------------ destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H49.
----------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H47.
------------------------ assert (* Cut *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H47.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder G A B H46).
------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H38.
------------------------ assert (* Cut *) (euclidean__axioms.Col E D W) as H48.
------------------------- assert (* Cut *) ((euclidean__axioms.Col W D E) /\ ((euclidean__axioms.Col W E D) /\ ((euclidean__axioms.Col E D W) /\ ((euclidean__axioms.Col D E W) /\ (euclidean__axioms.Col E W D))))) as H48.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder D W E H41).
-------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
------------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H49.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H49.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
--------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
-------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H50.
--------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D E H49).
--------------------------- assert (* Cut *) (euclidean__axioms.Col D G W) as H51.
---------------------------- apply (@euclidean__tactics.not__nCol__Col D G W).
-----------------------------intro H51.
apply (@euclidean__tactics.Col__nCol__False D G W H51).
------------------------------apply (@lemma__collinear4.lemma__collinear4 E D G W H47 H48 H50).


---------------------------- assert (* Cut *) (euclidean__axioms.Col G W D) as H52.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col G D W) /\ ((euclidean__axioms.Col G W D) /\ ((euclidean__axioms.Col W D G) /\ ((euclidean__axioms.Col D W G) /\ (euclidean__axioms.Col W G D))))) as H52.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D G W H51).
------------------------------ destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H55.
----------------------------- assert (* Cut *) (B = B) as H53.
------------------------------ apply (@logic.eq__refl Point B).
------------------------------ assert (* Cut *) (euclidean__axioms.Col A B B) as H54.
------------------------------- right.
right.
left.
exact H53.
------------------------------- assert (* Cut *) (euclidean__axioms.neq G W) as H55.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric W G H39).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col G W B) as H56.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col G W B).
----------------------------------intro H56.
apply (@euclidean__tactics.Col__nCol__False G W B H56).
-----------------------------------apply (@lemma__collinear5.lemma__collinear5 A B G W B H16 H6 H22 H54).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col W D B) as H57.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col W D B).
-----------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False W D B H57).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 G W D B H52 H56 H55).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col W B D) as H58.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col D W B) /\ ((euclidean__axioms.Col D B W) /\ ((euclidean__axioms.Col B W D) /\ ((euclidean__axioms.Col W B D) /\ (euclidean__axioms.Col B D W))))) as H58.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder W D B H57).
------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B A W) as H59.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B W A) /\ ((euclidean__axioms.Col B A W) /\ ((euclidean__axioms.Col A W B) /\ ((euclidean__axioms.Col W A B) /\ (euclidean__axioms.Col A B W))))) as H59.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder W B A H44).
------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A G) as H60.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H60.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G A B H46).
-------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H68.
------------------------------------- assert (* Cut *) (A = A) as H61.
-------------------------------------- apply (@logic.eq__refl Point A).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A A) as H62.
--------------------------------------- right.
right.
left.
exact H61.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col G W A) as H63.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col G W A).
-----------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False G W A H63).
------------------------------------------apply (@lemma__collinear5.lemma__collinear5 B A G W A H17 H60 H59 H62).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col W D A) as H64.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col W D A).
------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False W D A H64).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G W D A H52 H63 H55).


----------------------------------------- assert (* Cut *) (euclidean__axioms.neq D W) as H65.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H65.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq W D) as H66.
------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D W H65).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H67.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col D B A).
---------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False D B A H67).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 W D B A H57 H64 H66).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B D) as H68.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col D A B) /\ (euclidean__axioms.Col A B D))))) as H68.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D B A H67).
---------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
--------------------------------------------- apply (@H31).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col Q C D).
-----------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False A B D H23 H68).


---------------- assert (* Cut *) (euclidean__axioms.BetS D G E) as H40.
----------------- apply (@eq__ind euclidean__axioms.Point W (fun X => euclidean__axioms.BetS D X E)) with (y := G).
------------------ exact H20.
------------------apply (@euclidean__tactics.NNPP (W = G) H39).

----------------- assert (* Cut *) (euclidean__axioms.BetS E G D) as H41.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry D G E H40).
------------------ assert (euclidean__axioms.BetS G F D) as H42 by exact H37.
assert (* Cut *) (euclidean__axioms.BetS E G F) as H43.
------------------- apply (@euclidean__axioms.axiom__innertransitivity E G F D H41 H42).
------------------- assert (* Cut *) (~(euclidean__axioms.Col H3 C E)) as H44.
-------------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col H3 E C) as H45.
--------------------- assert (* Cut *) ((euclidean__axioms.Col C H3 E) /\ ((euclidean__axioms.Col C E H3) /\ ((euclidean__axioms.Col E H3 C) /\ ((euclidean__axioms.Col H3 E C) /\ (euclidean__axioms.Col E C H3))))) as H45.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 C E H44).
---------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H52.
--------------------- assert (* Cut *) (euclidean__axioms.Col E H3 C) as H46.
---------------------- assert (* Cut *) ((euclidean__axioms.Col E H3 C) /\ ((euclidean__axioms.Col E C H3) /\ ((euclidean__axioms.Col C H3 E) /\ ((euclidean__axioms.Col H3 C E) /\ (euclidean__axioms.Col C E H3))))) as H46.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 E C H45).
----------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H47.
---------------------- assert (* Cut *) (euclidean__axioms.Col C F H3) as H47.
----------------------- right.
right.
right.
right.
left.
exact H34.
----------------------- assert (* Cut *) (euclidean__axioms.Col H3 C F) as H48.
------------------------ assert (* Cut *) ((euclidean__axioms.Col F C H3) /\ ((euclidean__axioms.Col F H3 C) /\ ((euclidean__axioms.Col H3 C F) /\ ((euclidean__axioms.Col C H3 F) /\ (euclidean__axioms.Col H3 F C))))) as H48.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F H3 H47).
------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
------------------------ assert (* Cut *) (euclidean__axioms.Col H3 C E) as H49.
------------------------- assert (* Cut *) ((euclidean__axioms.Col C H3 F) /\ ((euclidean__axioms.Col C F H3) /\ ((euclidean__axioms.Col F H3 C) /\ ((euclidean__axioms.Col H3 F C) /\ (euclidean__axioms.Col F C H3))))) as H49.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 C F H48).
-------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H44.
------------------------- assert (* Cut *) (euclidean__axioms.neq C H3) as H50.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq F H3) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C H3))) as H50.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F H3 H34).
--------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H54.
-------------------------- assert (* Cut *) (euclidean__axioms.neq H3 C) as H51.
--------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C H3 H50).
--------------------------- assert (* Cut *) (euclidean__axioms.Col C F E) as H52.
---------------------------- apply (@euclidean__tactics.not__nCol__Col C F E).
-----------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False C F E H52).
------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 C F E H48 H49 H51).


---------------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H53.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))))) as H53.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C F E H52).
------------------------------ destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H61.
----------------------------- assert (* Cut *) (euclidean__axioms.BetS D F E) as H54.
------------------------------ apply (@lemma__3__6b.lemma__3__6b D F G E H35 H40).
------------------------------ assert (* Cut *) (euclidean__axioms.Col D F E) as H55.
------------------------------- right.
right.
right.
right.
left.
exact H54.
------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H56.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D))))) as H56.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D F E H55).
--------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H57.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D E))) as H57.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D F E H54).
---------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H58.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H58.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F E H57).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col F C D) as H59.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col F C D).
------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False F C D H59).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 E F C D H53 H56 H58).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col F D C) as H60.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C F D) /\ ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F D C) /\ (euclidean__axioms.Col D C F))))) as H60.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F C D H59).
------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H67.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col D F G) as H61.
------------------------------------- right.
right.
right.
right.
left.
exact H35.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D G) as H62.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col F G D) /\ ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col D G F) /\ (euclidean__axioms.Col G F D))))) as H62.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D F G H61).
--------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H63.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H63.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D E))) as H63.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D F E H54).
---------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H66.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H64.
---------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D F H63).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C G) as H65.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col D C G).
------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False D C G H65).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 F D C G H60 H62 H64).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C D) as H66.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D))))) as H66.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C G H65).
------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H74.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C G Q) as H67.
------------------------------------------- right.
right.
right.
right.
left.
exact H10.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C Q) as H68.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col G Q C) /\ ((euclidean__axioms.Col Q C G) /\ ((euclidean__axioms.Col C Q G) /\ (euclidean__axioms.Col Q G C))))) as H68.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G Q H67).
--------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H69.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H69.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D E))) as H69.
---------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D F E H54).
---------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H24.
--------------------------------------------- assert (euclidean__axioms.neq G C) as H70 by exact H25.
assert (* Cut *) (euclidean__axioms.Col C D Q) as H71.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C D Q).
-----------------------------------------------intro H71.
apply (@euclidean__tactics.Col__nCol__False C D Q H71).
------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G C D Q H66 H68 H70).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C D) as H72.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q C D) /\ ((euclidean__axioms.Col C Q D) /\ (euclidean__axioms.Col Q D C))))) as H72.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C D Q H71).
------------------------------------------------ destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
----------------------------------------------- apply (@H31 H72).
-------------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS H3 G M)) as H45.
--------------------- apply (@euclidean__axioms.postulate__Pasch__outer E H3 F G C H43 H36).
----------------------apply (@euclidean__tactics.nCol__notCol H3 C E H44).

--------------------- destruct H45 as [M H46].
destruct H46 as [H47 H48].
assert (* Cut *) (euclidean__axioms.Col H3 G M) as H49.
---------------------- right.
right.
right.
right.
left.
exact H48.
---------------------- assert (* Cut *) (euclidean__axioms.Col B H3 G) as H50.
----------------------- apply (@euclidean__tactics.not__nCol__Col B H3 G).
------------------------intro H50.
apply (@euclidean__tactics.Col__nCol__False B H3 G H50).
-------------------------apply (@lemma__collinear4.lemma__collinear4 A B H3 G H8 H6 H16).


----------------------- assert (* Cut *) (euclidean__axioms.Col H3 G B) as H51.
------------------------ assert (* Cut *) ((euclidean__axioms.Col H3 B G) /\ ((euclidean__axioms.Col H3 G B) /\ ((euclidean__axioms.Col G B H3) /\ ((euclidean__axioms.Col B G H3) /\ (euclidean__axioms.Col G H3 B))))) as H51.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder B H3 G H50).
------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H54.
------------------------ assert (* Cut *) (euclidean__axioms.neq H3 G) as H52.
------------------------- assert (* Cut *) ((euclidean__axioms.neq G M) /\ ((euclidean__axioms.neq H3 G) /\ (euclidean__axioms.neq H3 M))) as H52.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H3 G M H48).
-------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H55.
------------------------- assert (* Cut *) (euclidean__axioms.Col G M B) as H53.
-------------------------- apply (@euclidean__tactics.not__nCol__Col G M B).
---------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False G M B H53).
----------------------------apply (@lemma__collinear4.lemma__collinear4 H3 G M B H49 H51 H52).


-------------------------- assert (* Cut *) (euclidean__axioms.Col G B M) as H54.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col M B G) /\ ((euclidean__axioms.Col B G M) /\ ((euclidean__axioms.Col G B M) /\ (euclidean__axioms.Col B M G))))) as H54.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder G M B H53).
---------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H61.
--------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H55.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H55.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B G H6).
----------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H63.
---------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H56.
----------------------------- assert (* Cut *) ((B = G) \/ (euclidean__axioms.neq B G)) as H56.
------------------------------ apply (@euclidean__tactics.eq__or__neq B G).
------------------------------ assert ((B = G) \/ (euclidean__axioms.neq B G)) as H57 by exact H56.
assert ((B = G) \/ (euclidean__axioms.neq B G)) as __TmpHyp0 by exact H57.
destruct __TmpHyp0 as [H58|H58].
------------------------------- assert (* Cut *) (euclidean__axioms.Col B A H3) as H59.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A H3) /\ ((euclidean__axioms.Col B H3 A) /\ ((euclidean__axioms.Col H3 A B) /\ ((euclidean__axioms.Col A H3 B) /\ (euclidean__axioms.Col H3 B A))))) as H59.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B H3 H8).
--------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B A G) as H60.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H60.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G B A H55).
---------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H63.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col A H3 G) as H61.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col A H3 G).
-----------------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False A H3 G H61).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 B A H3 G H59 H60 H17).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 G A) as H62.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 A G) /\ ((euclidean__axioms.Col H3 G A) /\ ((euclidean__axioms.Col G A H3) /\ ((euclidean__axioms.Col A G H3) /\ (euclidean__axioms.Col G H3 A))))) as H62.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A H3 G H61).
------------------------------------ destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H65.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col G A M) as H63.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col G A M).
-------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False G A M H63).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 G A M H62 H49 H52).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A M) as H64.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun B0 => (euclidean__defs.OS C D A B0) -> ((euclidean__axioms.TS D A B0 E) -> ((euclidean__axioms.Col A B0 G) -> ((euclidean__axioms.Col A B0 H3) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__axioms.nCol A B0 D) -> ((~(A = B0)) -> ((euclidean__axioms.neq B0 A) -> ((euclidean__axioms.Col A B0 W) -> ((euclidean__axioms.nCol A B0 D) -> ((~(euclidean__axioms.TS C A B0 E)) -> ((euclidean__axioms.Col B0 H3 G) -> ((euclidean__axioms.Col H3 G B0) -> ((euclidean__axioms.Col G M B0) -> ((euclidean__axioms.Col G B0 M) -> ((euclidean__axioms.Col G B0 A) -> ((euclidean__axioms.Col B0 A H3) -> ((euclidean__axioms.Col B0 A G) -> (euclidean__axioms.Col B0 A M)))))))))))))))))))) with (x := B).
--------------------------------------intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
exact H63.

-------------------------------------- exact H58.
-------------------------------------- exact H.
-------------------------------------- exact H0.
-------------------------------------- exact H6.
-------------------------------------- exact H8.
-------------------------------------- exact H14.
-------------------------------------- exact H15.
-------------------------------------- exact H16.
-------------------------------------- exact H17.
-------------------------------------- exact H22.
-------------------------------------- exact H23.
-------------------------------------- exact H30.
-------------------------------------- exact H50.
-------------------------------------- exact H51.
-------------------------------------- exact H53.
-------------------------------------- exact H54.
-------------------------------------- exact H55.
-------------------------------------- exact H59.
-------------------------------------- exact H60.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H65.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col A M B) /\ ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col B M A) /\ (euclidean__axioms.Col M A B))))) as H65.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A M H64).
--------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H66.
-------------------------------------- exact H65.
------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H59.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B G H58).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B M A) as H60.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col B M A).
----------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False B M A H60).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 G B M A H54 H55 H59).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H61.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H61.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M A H60).
----------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
---------------------------------- exact H61.
----------------------------- assert (* Cut *) (euclidean__axioms.BetS C M E) as H57.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry E M C H47).
------------------------------ assert (* Cut *) (euclidean__axioms.TS C A B E) as H58.
------------------------------- exists M.
split.
-------------------------------- exact H57.
-------------------------------- split.
--------------------------------- exact H56.
--------------------------------- exact H14.
------------------------------- apply (@H30 H58).
--------------- assert (* Cut *) (euclidean__axioms.TS F A B E) as H39.
---------------- apply (@lemma__9__5b.lemma__9__5b A B E D F G H0 H37).
-----------------apply (@euclidean__tactics.nCol__notCol E D G H38).

----------------- exact H6.
---------------- assert (* Cut *) (~(G = H3)) as H40.
----------------- intro H40.
assert (* Cut *) (euclidean__axioms.Col D H3 Q) as H41.
------------------ right.
right.
right.
right.
left.
exact H12.
------------------ assert (* Cut *) (euclidean__axioms.Col C G Q) as H42.
------------------- right.
right.
right.
right.
left.
exact H10.
------------------- assert (* Cut *) (euclidean__axioms.Col Q H3 D) as H43.
-------------------- assert (* Cut *) ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col H3 Q D) /\ ((euclidean__axioms.Col Q D H3) /\ ((euclidean__axioms.Col D Q H3) /\ (euclidean__axioms.Col Q H3 D))))) as H43.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder D H3 Q H41).
--------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H51.
-------------------- assert (* Cut *) (euclidean__axioms.Col Q G C) as H44.
--------------------- assert (* Cut *) ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col G Q C) /\ ((euclidean__axioms.Col Q C G) /\ ((euclidean__axioms.Col C Q G) /\ (euclidean__axioms.Col Q G C))))) as H44.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder C G Q H42).
---------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
--------------------- assert (* Cut *) (euclidean__axioms.Col Q H3 C) as H45.
---------------------- apply (@eq__ind__r euclidean__axioms.Point H3 (fun G0 => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.BetS C G0 Q) -> ((euclidean__axioms.neq C G0) -> ((euclidean__axioms.neq G0 C) -> ((euclidean__axioms.neq G0 Q) -> ((euclidean__axioms.BetS D F G0) -> ((euclidean__axioms.BetS G0 F D) -> ((~(euclidean__axioms.Col E D G0)) -> ((euclidean__axioms.Col C G0 Q) -> ((euclidean__axioms.Col Q G0 C) -> (euclidean__axioms.Col Q H3 C)))))))))))) with (x := G).
-----------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
exact H54.

----------------------- exact H40.
----------------------- exact H6.
----------------------- exact H10.
----------------------- exact H24.
----------------------- exact H25.
----------------------- exact H26.
----------------------- exact H35.
----------------------- exact H37.
----------------------- exact H38.
----------------------- exact H42.
----------------------- exact H44.
---------------------- assert (* Cut *) (euclidean__axioms.neq H3 Q) as H46.
----------------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H46.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
------------------------ destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H47.
----------------------- assert (* Cut *) (euclidean__axioms.neq Q H3) as H47.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H3 Q H46).
------------------------ assert (* Cut *) (euclidean__axioms.Col H3 D C) as H48.
------------------------- apply (@euclidean__tactics.not__nCol__Col H3 D C).
--------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False H3 D C H48).
---------------------------apply (@lemma__collinear4.lemma__collinear4 Q H3 D C H43 H45 H47).


------------------------- assert (* Cut *) (euclidean__axioms.Col H3 D Q) as H49.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 Q D) /\ ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col D Q H3) /\ ((euclidean__axioms.Col Q D H3) /\ (euclidean__axioms.Col D H3 Q))))) as H49.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q H3 D H43).
--------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H52.
-------------------------- assert (* Cut *) (euclidean__axioms.neq D H3) as H50.
--------------------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H50.
---------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
---------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H53.
--------------------------- assert (* Cut *) (euclidean__axioms.neq H3 D) as H51.
---------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D H3 H50).
---------------------------- assert (* Cut *) (euclidean__axioms.Col D C Q) as H52.
----------------------------- apply (@euclidean__tactics.not__nCol__Col D C Q).
------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False D C Q H52).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 D C Q H48 H49 H51).


----------------------------- assert (* Cut *) (euclidean__axioms.Col C Q D) as H53.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col Q D C) /\ ((euclidean__axioms.Col D Q C) /\ (euclidean__axioms.Col Q C D))))) as H53.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C Q H52).
------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H56.
------------------------------ apply (@H31).
-------------------------------apply (@euclidean__tactics.not__nCol__Col Q C D).
--------------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False C Q D H29 H53).


----------------- assert (* Cut *) (~(euclidean__axioms.Col H3 C E)) as H41.
------------------ intro H41.
assert (* Cut *) (exists K, (euclidean__axioms.BetS G K H3) /\ (euclidean__axioms.Cong K G K H3)) as H42.
------------------- apply (@proposition__10.proposition__10 G H3 H40).
------------------- destruct H42 as [K H43].
destruct H43 as [H44 H45].
assert (* Cut *) (~(euclidean__axioms.Col G D E)) as H46.
-------------------- intro H46.
assert (* Cut *) (euclidean__axioms.Col E D G) as H47.
--------------------- assert (* Cut *) ((euclidean__axioms.Col D G E) /\ ((euclidean__axioms.Col D E G) /\ ((euclidean__axioms.Col E G D) /\ ((euclidean__axioms.Col G E D) /\ (euclidean__axioms.Col E D G))))) as H47.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder G D E H46).
---------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
--------------------- apply (@H31).
----------------------apply (@euclidean__tactics.not__nCol__Col Q C D).
-----------------------intro H48.
apply (@H38 H47).


-------------------- assert (* Cut *) (euclidean__axioms.BetS E W D) as H47.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D W E H20).
--------------------- assert (euclidean__axioms.BetS G F D) as H48 by exact H37.
assert (* Cut *) (exists J, (euclidean__axioms.BetS E J F) /\ (euclidean__axioms.BetS G J W)) as H49.
---------------------- apply (@euclidean__axioms.postulate__Pasch__inner E G D W F H47 H48).
-----------------------apply (@euclidean__tactics.nCol__notCol E D G H38).

---------------------- destruct H49 as [J H50].
destruct H50 as [H51 H52].
assert (* Cut *) (euclidean__axioms.Col G J W) as H53.
----------------------- right.
right.
right.
right.
left.
exact H52.
----------------------- assert (* Cut *) (euclidean__axioms.Col E F J) as H54.
------------------------ right.
right.
right.
right.
right.
exact H51.
------------------------ assert (* Cut *) (euclidean__axioms.Col E C H3) as H55.
------------------------- assert (* Cut *) ((euclidean__axioms.Col C H3 E) /\ ((euclidean__axioms.Col C E H3) /\ ((euclidean__axioms.Col E H3 C) /\ ((euclidean__axioms.Col H3 E C) /\ (euclidean__axioms.Col E C H3))))) as H55.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 C E H41).
-------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H63.
------------------------- assert (* Cut *) (euclidean__axioms.Col F E J) as H56.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col F E J) /\ ((euclidean__axioms.Col F J E) /\ ((euclidean__axioms.Col J E F) /\ ((euclidean__axioms.Col E J F) /\ (euclidean__axioms.Col J F E))))) as H56.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F J H54).
--------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H57.
-------------------------- assert (* Cut *) (euclidean__axioms.Col C F H3) as H57.
--------------------------- right.
right.
right.
right.
left.
exact H34.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C H3 F) as H58.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col F C H3) /\ ((euclidean__axioms.Col F H3 C) /\ ((euclidean__axioms.Col H3 C F) /\ ((euclidean__axioms.Col C H3 F) /\ (euclidean__axioms.Col H3 F C))))) as H58.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F H3 H57).
----------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
---------------------------- assert (* Cut *) (euclidean__axioms.Col C H3 E) as H59.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col C E H3) /\ ((euclidean__axioms.Col C H3 E) /\ ((euclidean__axioms.Col H3 E C) /\ ((euclidean__axioms.Col E H3 C) /\ (euclidean__axioms.Col H3 C E))))) as H59.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E C H3 H55).
------------------------------ destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
----------------------------- assert (* Cut *) (euclidean__axioms.neq C H3) as H60.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq F H3) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C H3))) as H60.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F H3 H34).
------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
------------------------------ assert (* Cut *) (euclidean__axioms.Col H3 F E) as H61.
------------------------------- apply (@euclidean__tactics.not__nCol__Col H3 F E).
--------------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False H3 F E H61).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 C H3 F E H58 H59 H60).


------------------------------- assert (* Cut *) (euclidean__axioms.Col F E H3) as H62.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col F H3 E) /\ ((euclidean__axioms.Col F E H3) /\ ((euclidean__axioms.Col E H3 F) /\ ((euclidean__axioms.Col H3 E F) /\ (euclidean__axioms.Col E F H3))))) as H62.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 F E H61).
--------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H65.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H63.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq E J) /\ (euclidean__axioms.neq E F))) as H63.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E J F H51).
---------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H67.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H64.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E F H63).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col E J H3) as H65.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col E J H3).
------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False E J H3 H65).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 F E J H3 H56 H62 H64).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col E H3 J) as H66.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col J E H3) /\ ((euclidean__axioms.Col J H3 E) /\ ((euclidean__axioms.Col H3 E J) /\ ((euclidean__axioms.Col E H3 J) /\ (euclidean__axioms.Col H3 J E))))) as H66.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E J H3 H65).
------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col G W J) as H67.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J G W) /\ ((euclidean__axioms.Col J W G) /\ ((euclidean__axioms.Col W G J) /\ ((euclidean__axioms.Col G W J) /\ (euclidean__axioms.Col W J G))))) as H67.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G J W H53).
-------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H74.
------------------------------------- assert (* Cut *) (H3 = H3) as H68.
-------------------------------------- apply (@logic.eq__refl Point H3).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H3 H3) as H69.
--------------------------------------- right.
right.
left.
exact H68.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H3 W) as H70.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col G H3 W).
-----------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False G H3 W H70).
------------------------------------------apply (@lemma__collinear5.lemma__collinear5 A B G H3 W H16 H6 H8 H22).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col G W H3) as H71.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 G W) /\ ((euclidean__axioms.Col H3 W G) /\ ((euclidean__axioms.Col W G H3) /\ ((euclidean__axioms.Col G W H3) /\ (euclidean__axioms.Col W H3 G))))) as H71.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G H3 W H70).
------------------------------------------ destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
----------------------------------------- assert (* Cut *) (~(G = W)) as H72.
------------------------------------------ intro H72.
assert (* Cut *) (euclidean__axioms.Col D W E) as H73.
------------------------------------------- right.
right.
right.
right.
left.
exact H20.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G E) as H74.
-------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point W (fun G0 => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.BetS C G0 Q) -> ((euclidean__axioms.neq C G0) -> ((euclidean__axioms.neq G0 C) -> ((euclidean__axioms.neq G0 Q) -> ((euclidean__axioms.BetS D F G0) -> ((euclidean__axioms.BetS G0 F D) -> ((~(euclidean__axioms.Col E D G0)) -> ((~(G0 = H3)) -> ((euclidean__axioms.BetS G0 K H3) -> ((euclidean__axioms.Cong K G0 K H3) -> ((~(euclidean__axioms.Col G0 D E)) -> ((euclidean__axioms.BetS G0 F D) -> ((euclidean__axioms.BetS G0 J W) -> ((euclidean__axioms.Col G0 J W) -> ((euclidean__axioms.Col G0 W J) -> ((euclidean__axioms.Col G0 H3 W) -> ((euclidean__axioms.Col G0 W H3) -> (euclidean__axioms.Col D G0 E)))))))))))))))))))) with (x := G).
---------------------------------------------intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
exact H73.

--------------------------------------------- exact H72.
--------------------------------------------- exact H6.
--------------------------------------------- exact H10.
--------------------------------------------- exact H24.
--------------------------------------------- exact H25.
--------------------------------------------- exact H26.
--------------------------------------------- exact H35.
--------------------------------------------- exact H37.
--------------------------------------------- exact H38.
--------------------------------------------- exact H40.
--------------------------------------------- exact H44.
--------------------------------------------- exact H45.
--------------------------------------------- exact H46.
--------------------------------------------- exact H48.
--------------------------------------------- exact H52.
--------------------------------------------- exact H53.
--------------------------------------------- exact H67.
--------------------------------------------- exact H70.
--------------------------------------------- exact H71.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H75.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col G E D) /\ ((euclidean__axioms.Col E D G) /\ ((euclidean__axioms.Col D E G) /\ (euclidean__axioms.Col E G D))))) as H75.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D G E H74).
---------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H80.
--------------------------------------------- apply (@H31).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col Q C D).
-----------------------------------------------intro H76.
apply (@H38 H75).


------------------------------------------ assert (euclidean__axioms.Col E J H3) as H73 by exact H65.
assert (* Cut *) (euclidean__axioms.Col W J H3) as H74.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col W J H3).
--------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False W J H3 H74).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G W J H3 H67 H71 H72).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H3 E) as H75.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J E H3) /\ ((euclidean__axioms.Col J H3 E) /\ ((euclidean__axioms.Col H3 E J) /\ ((euclidean__axioms.Col E H3 J) /\ (euclidean__axioms.Col H3 J E))))) as H75.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E J H3 H73).
--------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H78.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H3 W) as H76.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J W H3) /\ ((euclidean__axioms.Col J H3 W) /\ ((euclidean__axioms.Col H3 W J) /\ ((euclidean__axioms.Col W H3 J) /\ (euclidean__axioms.Col H3 J W))))) as H76.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder W J H3 H74).
---------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H79.
--------------------------------------------- assert (* Cut *) (~(H3 = W)) as H77.
---------------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col D W E) as H78.
----------------------------------------------- right.
right.
right.
right.
left.
exact H20.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H3 E) as H79.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point W (fun H79 => (euclidean__axioms.Col A B H79) -> ((euclidean__axioms.BetS D H79 Q) -> ((euclidean__axioms.BetS C F H79) -> ((euclidean__axioms.BetS H79 F C) -> ((~(G = H79)) -> ((euclidean__axioms.Col H79 C E) -> ((euclidean__axioms.BetS G K H79) -> ((euclidean__axioms.Cong K G K H79) -> ((euclidean__axioms.Col E C H79) -> ((euclidean__axioms.Col C F H79) -> ((euclidean__axioms.Col C H79 F) -> ((euclidean__axioms.Col C H79 E) -> ((euclidean__axioms.neq C H79) -> ((euclidean__axioms.Col H79 F E) -> ((euclidean__axioms.Col F E H79) -> ((euclidean__axioms.Col E J H79) -> ((euclidean__axioms.Col E H79 J) -> ((H79 = H79) -> ((euclidean__axioms.Col E H79 H79) -> ((euclidean__axioms.Col G H79 W) -> ((euclidean__axioms.Col G W H79) -> ((euclidean__axioms.Col E J H79) -> ((euclidean__axioms.Col W J H79) -> ((euclidean__axioms.Col J H79 E) -> ((euclidean__axioms.Col J H79 W) -> (euclidean__axioms.Col D H79 E))))))))))))))))))))))))))) with (x := H3).
-------------------------------------------------intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
exact H78.

------------------------------------------------- exact H77.
------------------------------------------------- exact H8.
------------------------------------------------- exact H12.
------------------------------------------------- exact H34.
------------------------------------------------- exact H36.
------------------------------------------------- exact H40.
------------------------------------------------- exact H41.
------------------------------------------------- exact H44.
------------------------------------------------- exact H45.
------------------------------------------------- exact H55.
------------------------------------------------- exact H57.
------------------------------------------------- exact H58.
------------------------------------------------- exact H59.
------------------------------------------------- exact H60.
------------------------------------------------- exact H61.
------------------------------------------------- exact H62.
------------------------------------------------- exact H65.
------------------------------------------------- exact H66.
------------------------------------------------- exact H68.
------------------------------------------------- exact H69.
------------------------------------------------- exact H70.
------------------------------------------------- exact H71.
------------------------------------------------- exact H73.
------------------------------------------------- exact H74.
------------------------------------------------- exact H75.
------------------------------------------------- exact H76.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D H3 Q) as H80.
------------------------------------------------- right.
right.
right.
right.
left.
exact H12.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D H3) as H81.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H81.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
--------------------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H84.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 E Q) as H82.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H3 E Q).
----------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False H3 E Q H82).
-----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D H3 E Q H79 H80 H81).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 E C) as H83.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 C E) /\ ((euclidean__axioms.Col H3 E C) /\ ((euclidean__axioms.Col E C H3) /\ ((euclidean__axioms.Col C E H3) /\ (euclidean__axioms.Col E H3 C))))) as H83.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C H3 E H59).
----------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H86.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq W E) as H84.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H84.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
------------------------------------------------------ destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H85.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H3 E) as H85.
------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point W (fun H85 => (euclidean__axioms.Col A B H85) -> ((euclidean__axioms.BetS D H85 Q) -> ((euclidean__axioms.BetS C F H85) -> ((euclidean__axioms.BetS H85 F C) -> ((~(G = H85)) -> ((euclidean__axioms.Col H85 C E) -> ((euclidean__axioms.BetS G K H85) -> ((euclidean__axioms.Cong K G K H85) -> ((euclidean__axioms.Col E C H85) -> ((euclidean__axioms.Col C F H85) -> ((euclidean__axioms.Col C H85 F) -> ((euclidean__axioms.Col C H85 E) -> ((euclidean__axioms.neq C H85) -> ((euclidean__axioms.Col H85 F E) -> ((euclidean__axioms.Col F E H85) -> ((euclidean__axioms.Col E J H85) -> ((euclidean__axioms.Col E H85 J) -> ((H85 = H85) -> ((euclidean__axioms.Col E H85 H85) -> ((euclidean__axioms.Col G H85 W) -> ((euclidean__axioms.Col G W H85) -> ((euclidean__axioms.Col E J H85) -> ((euclidean__axioms.Col W J H85) -> ((euclidean__axioms.Col J H85 E) -> ((euclidean__axioms.Col J H85 W) -> ((euclidean__axioms.Col D H85 E) -> ((euclidean__axioms.Col D H85 Q) -> ((euclidean__axioms.neq D H85) -> ((euclidean__axioms.Col H85 E Q) -> ((euclidean__axioms.Col H85 E C) -> (euclidean__axioms.neq H85 E)))))))))))))))))))))))))))))))) with (x := H3).
-------------------------------------------------------intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
exact H84.

------------------------------------------------------- exact H77.
------------------------------------------------------- exact H8.
------------------------------------------------------- exact H12.
------------------------------------------------------- exact H34.
------------------------------------------------------- exact H36.
------------------------------------------------------- exact H40.
------------------------------------------------------- exact H41.
------------------------------------------------------- exact H44.
------------------------------------------------------- exact H45.
------------------------------------------------------- exact H55.
------------------------------------------------------- exact H57.
------------------------------------------------------- exact H58.
------------------------------------------------------- exact H59.
------------------------------------------------------- exact H60.
------------------------------------------------------- exact H61.
------------------------------------------------------- exact H62.
------------------------------------------------------- exact H65.
------------------------------------------------------- exact H66.
------------------------------------------------------- exact H68.
------------------------------------------------------- exact H69.
------------------------------------------------------- exact H70.
------------------------------------------------------- exact H71.
------------------------------------------------------- exact H73.
------------------------------------------------------- exact H74.
------------------------------------------------------- exact H75.
------------------------------------------------------- exact H76.
------------------------------------------------------- exact H79.
------------------------------------------------------- exact H80.
------------------------------------------------------- exact H81.
------------------------------------------------------- exact H82.
------------------------------------------------------- exact H83.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E Q C) as H86.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E Q C).
--------------------------------------------------------intro H86.
apply (@euclidean__tactics.Col__nCol__False E Q C H86).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 E Q C H82 H83 H85).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C Q) as H87.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q E C) /\ ((euclidean__axioms.Col Q C E) /\ ((euclidean__axioms.Col C E Q) /\ ((euclidean__axioms.Col E C Q) /\ (euclidean__axioms.Col C Q E))))) as H87.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E Q C H86).
--------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H94.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C H3) as H88.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C E Q) /\ ((euclidean__axioms.Col C Q E) /\ ((euclidean__axioms.Col Q E C) /\ ((euclidean__axioms.Col E Q C) /\ (euclidean__axioms.Col Q C E))))) as H88.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E C Q H87).
---------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H55.
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq E C)) as H89.
---------------------------------------------------------- intro H89.
assert (* Cut *) (euclidean__axioms.Col C Q H3) as H90.
----------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C Q H3).
------------------------------------------------------------intro H90.
apply (@euclidean__tactics.Col__nCol__False C Q H3 H90).
-------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 E C Q H3 H87 H88 H89).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 Q C) as H91.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col Q C H3) /\ ((euclidean__axioms.Col Q H3 C) /\ ((euclidean__axioms.Col H3 C Q) /\ ((euclidean__axioms.Col C H3 Q) /\ (euclidean__axioms.Col H3 Q C))))) as H91.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C Q H3 H90).
------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H99.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H3 Q D) as H92.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col H3 Q D) /\ ((euclidean__axioms.Col Q D H3) /\ ((euclidean__axioms.Col D Q H3) /\ (euclidean__axioms.Col Q H3 D))))) as H92.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D H3 Q H80).
-------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H95.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H3 Q) as H93.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H93.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
--------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H94.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C D) as H94.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col Q C D).
----------------------------------------------------------------intro H94.
apply (@H31).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 Q C D H91 H92 H93).


--------------------------------------------------------------- apply (@H31 H94).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E W D) as H90.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col W D E) /\ ((euclidean__axioms.Col W E D) /\ ((euclidean__axioms.Col E D W) /\ ((euclidean__axioms.Col D E W) /\ (euclidean__axioms.Col E W D))))) as H90.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D W E H78).
------------------------------------------------------------ destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H98.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C W D) as H91.
------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point E (fun X => euclidean__axioms.Col X W D)) with (y := C).
------------------------------------------------------------- exact H90.
-------------------------------------------------------------apply (@euclidean__tactics.NNPP (E = C) H89).

------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C H3 D) as H92.
------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point W (fun H92 => (euclidean__axioms.Col A B H92) -> ((euclidean__axioms.BetS D H92 Q) -> ((euclidean__axioms.BetS C F H92) -> ((euclidean__axioms.BetS H92 F C) -> ((~(G = H92)) -> ((euclidean__axioms.Col H92 C E) -> ((euclidean__axioms.BetS G K H92) -> ((euclidean__axioms.Cong K G K H92) -> ((euclidean__axioms.Col E C H92) -> ((euclidean__axioms.Col C F H92) -> ((euclidean__axioms.Col C H92 F) -> ((euclidean__axioms.Col C H92 E) -> ((euclidean__axioms.neq C H92) -> ((euclidean__axioms.Col H92 F E) -> ((euclidean__axioms.Col F E H92) -> ((euclidean__axioms.Col E J H92) -> ((euclidean__axioms.Col E H92 J) -> ((H92 = H92) -> ((euclidean__axioms.Col E H92 H92) -> ((euclidean__axioms.Col G H92 W) -> ((euclidean__axioms.Col G W H92) -> ((euclidean__axioms.Col E J H92) -> ((euclidean__axioms.Col W J H92) -> ((euclidean__axioms.Col J H92 E) -> ((euclidean__axioms.Col J H92 W) -> ((euclidean__axioms.Col D H92 E) -> ((euclidean__axioms.Col D H92 Q) -> ((euclidean__axioms.neq D H92) -> ((euclidean__axioms.Col H92 E Q) -> ((euclidean__axioms.Col H92 E C) -> ((euclidean__axioms.neq H92 E) -> ((euclidean__axioms.Col E C H92) -> (euclidean__axioms.Col C H92 D)))))))))))))))))))))))))))))))))) with (x := H3).
--------------------------------------------------------------intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
exact H91.

-------------------------------------------------------------- exact H77.
-------------------------------------------------------------- exact H8.
-------------------------------------------------------------- exact H12.
-------------------------------------------------------------- exact H34.
-------------------------------------------------------------- exact H36.
-------------------------------------------------------------- exact H40.
-------------------------------------------------------------- exact H41.
-------------------------------------------------------------- exact H44.
-------------------------------------------------------------- exact H45.
-------------------------------------------------------------- exact H55.
-------------------------------------------------------------- exact H57.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- exact H59.
-------------------------------------------------------------- exact H60.
-------------------------------------------------------------- exact H61.
-------------------------------------------------------------- exact H62.
-------------------------------------------------------------- exact H65.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- exact H69.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- exact H75.
-------------------------------------------------------------- exact H76.
-------------------------------------------------------------- exact H79.
-------------------------------------------------------------- exact H80.
-------------------------------------------------------------- exact H81.
-------------------------------------------------------------- exact H82.
-------------------------------------------------------------- exact H83.
-------------------------------------------------------------- exact H85.
-------------------------------------------------------------- exact H88.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H3 C) as H93.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H3 C D) /\ ((euclidean__axioms.Col H3 D C) /\ ((euclidean__axioms.Col D C H3) /\ ((euclidean__axioms.Col C D H3) /\ (euclidean__axioms.Col D H3 C))))) as H93.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C H3 D H92).
--------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H101.
-------------------------------------------------------------- assert (euclidean__axioms.Col D H3 Q) as H94 by exact H80.
assert (* Cut *) (euclidean__axioms.neq D H3) as H95.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J W) /\ ((euclidean__axioms.neq G J) /\ (euclidean__axioms.neq G W))) as H95.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G J W H52).
---------------------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H81.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 C Q) as H96.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H3 C Q).
-----------------------------------------------------------------intro H96.
apply (@euclidean__tactics.Col__nCol__False H3 C Q H96).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D H3 C Q H93 H94 H95).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 Q C) as H97.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H3 Q) /\ ((euclidean__axioms.Col C Q H3) /\ ((euclidean__axioms.Col Q H3 C) /\ ((euclidean__axioms.Col H3 Q C) /\ (euclidean__axioms.Col Q C H3))))) as H97.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder H3 C Q H96).
------------------------------------------------------------------ destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H104.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 Q D) as H98.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H3 D Q) /\ ((euclidean__axioms.Col H3 Q D) /\ ((euclidean__axioms.Col Q D H3) /\ ((euclidean__axioms.Col D Q H3) /\ (euclidean__axioms.Col Q H3 D))))) as H98.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D H3 Q H94).
------------------------------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H101.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H3 Q) as H99.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H3 Q) /\ ((euclidean__axioms.neq D H3) /\ (euclidean__axioms.neq D Q))) as H99.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H3 Q H12).
-------------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H100.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C D) as H100.
-------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col Q C D).
---------------------------------------------------------------------intro H100.
apply (@H31).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 Q C D H97 H98 H99).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C Q D) as H101.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C Q D) /\ ((euclidean__axioms.Col C D Q) /\ ((euclidean__axioms.Col D Q C) /\ ((euclidean__axioms.Col Q D C) /\ (euclidean__axioms.Col D C Q))))) as H101.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q C D H100).
---------------------------------------------------------------------- destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
exact H102.
--------------------------------------------------------------------- apply (@H31 H100).
---------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq J H3)) as H78.
----------------------------------------------- intro H78.
assert (* Cut *) (euclidean__axioms.Col H3 E W) as H79.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col H3 E W).
-------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False H3 E W H79).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 J H3 E W H75 H76 H78).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H3 W E) as H80.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H3 W) /\ ((euclidean__axioms.Col E W H3) /\ ((euclidean__axioms.Col W H3 E) /\ ((euclidean__axioms.Col H3 W E) /\ (euclidean__axioms.Col W E H3))))) as H80.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H3 E W H79).
-------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H87.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H3 W G) as H81.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col W G H3) /\ ((euclidean__axioms.Col W H3 G) /\ ((euclidean__axioms.Col H3 G W) /\ ((euclidean__axioms.Col G H3 W) /\ (euclidean__axioms.Col H3 W G))))) as H81.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G W H3 H71).
--------------------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H89.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col W E G) as H82.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col W E G).
----------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False W E G H82).
-----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H3 W E G H80 H81 H77).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D W E) as H83.
---------------------------------------------------- right.
right.
right.
right.
left.
exact H20.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col W E D) as H84.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col W D E) /\ ((euclidean__axioms.Col W E D) /\ ((euclidean__axioms.Col E D W) /\ ((euclidean__axioms.Col D E W) /\ (euclidean__axioms.Col E W D))))) as H84.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D W E H83).
------------------------------------------------------ destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H87.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq W E) as H85.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq W E) /\ ((euclidean__axioms.neq D W) /\ (euclidean__axioms.neq D E))) as H85.
------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D W E H20).
------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H86.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E G D) as H86.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E G D).
--------------------------------------------------------intro H86.
apply (@H38).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 W E D G H84 H82 H85).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D G) as H87.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G E D) /\ ((euclidean__axioms.Col G D E) /\ ((euclidean__axioms.Col D E G) /\ ((euclidean__axioms.Col E D G) /\ (euclidean__axioms.Col D G E))))) as H87.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E G D H86).
--------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H94.
-------------------------------------------------------- apply (@H31).
---------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col Q C D).
----------------------------------------------------------intro H88.
apply (@H38 H87).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E H3 F) as H79.
------------------------------------------------ apply (@eq__ind euclidean__axioms.Point J (fun X => euclidean__axioms.BetS E X F)) with (y := H3).
------------------------------------------------- exact H51.
-------------------------------------------------apply (@euclidean__tactics.NNPP (J = H3) H78).

------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS F H3 E) as H80.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E H3 F H79).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H3 E) as H81.
-------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a C F H3 E H34 H80).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B E) as H82.
--------------------------------------------------- exists H3.
split.
---------------------------------------------------- exact H81.
---------------------------------------------------- split.
----------------------------------------------------- exact H8.
----------------------------------------------------- exact H14.
--------------------------------------------------- apply (@H30 H82).
------------------ assert (* Cut *) (euclidean__axioms.TS C A B E) as H42.
------------------- apply (@lemma__9__5a.lemma__9__5a A B E F C H3 H39 H36).
--------------------apply (@euclidean__tactics.nCol__notCol H3 C E H41).

-------------------- exact H8.
------------------- apply (@H30 H42).
---------- apply (@euclidean__tactics.NNPP (euclidean__axioms.TS C A B E)).
-----------intro H31.
destruct H14 as [H32 H33].
destruct H15 as [H34 H35].
destruct H23 as [H36 H37].
destruct H29 as [H38 H39].
destruct H33 as [H40 H41].
destruct H35 as [H42 H43].
destruct H37 as [H44 H45].
destruct H39 as [H46 H47].
destruct H41 as [H48 H49].
destruct H43 as [H50 H51].
destruct H45 as [H52 H53].
destruct H47 as [H54 H55].
destruct H49 as [H56 H57].
destruct H51 as [H58 H59].
destruct H53 as [H60 H61].
destruct H55 as [H62 H63].
destruct H57 as [H64 H65].
destruct H59 as [H66 H67].
destruct H61 as [H68 H69].
destruct H63 as [H70 H71].
assert (* Cut *) (False) as H72.
------------ apply (@H30 H31).
------------ contradiction H72.

------- exact H27.
Qed.
