Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplements.
Require Export lemma__supplementsymmetric.
Require Export logic.
Require Export proposition__27.
Definition proposition__28B : forall A B C D G H, (euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS C H D) -> ((euclidean__defs.RT B G H G H D) -> ((euclidean__defs.OS B D G H) -> (euclidean__defs.Par A B C D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__defs.OS D B G H) as H4.
- assert (* Cut *) ((euclidean__defs.OS D B G H) /\ ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G))) as H4.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric G H B D H3).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H5.
- assert (* Cut *) (exists a b c d e, (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d))) as H5.
-- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA B G H X Y U) /\ (euclidean__defs.CongA G H D V Y Z))) as H5 by exact H2.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA B G H X Y U) /\ (euclidean__defs.CongA G H D V Y Z))) as __TmpHyp by exact H5.
destruct __TmpHyp as [x H6].
destruct H6 as [x0 H7].
destruct H7 as [x1 H8].
destruct H8 as [x2 H9].
destruct H9 as [x3 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exists x.
exists x0.
exists x2.
exists x1.
exists x3.
split.
--- exact H11.
--- split.
---- exact H13.
---- exact H14.
-- destruct H5 as [a H6].
destruct H6 as [b H7].
destruct H7 as [c H8].
destruct H8 as [d H9].
destruct H9 as [e H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__defs.CongA a b c B G H) as H15.
--- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B G H a b c H13).
--- assert (* Cut *) (euclidean__axioms.neq G H) as H16.
---- assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H)))))) as H16.
----- apply (@lemma__angledistinct.lemma__angledistinct a b c B G H H15).
----- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H25.
---- assert (* Cut *) (euclidean__defs.CongA e b d G H D) as H17.
----- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric G H D e b d H14).
----- assert (* Cut *) (H = H) as H18.
------ apply (@logic.eq__refl Point H).
------ assert (* Cut *) (euclidean__defs.Out G H H) as H19.
------- apply (@lemma__ray4.lemma__ray4 G H H).
--------right.
left.
exact H18.

-------- exact H16.
------- assert (* Cut *) (euclidean__defs.Supp A G H H B) as H20.
-------- split.
--------- exact H19.
--------- exact H0.
-------- assert (* Cut *) (euclidean__defs.Supp B G H H A) as H21.
--------- apply (@lemma__supplementsymmetric.lemma__supplementsymmetric A G H B H H20).
--------- assert (* Cut *) (euclidean__defs.CongA e b d H G A) as H22.
---------- apply (@lemma__supplements.lemma__supplements a b c e d B G H H A H15 H11 H21).
---------- assert (euclidean__defs.CongA G H D e b d) as H23 by exact H14.
assert (* Cut *) (euclidean__defs.CongA G H D H G A) as H24.
----------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive G H D e b d H G A H23 H22).
----------- assert (* Cut *) (euclidean__axioms.nCol H G A) as H25.
------------ apply (@euclidean__tactics.nCol__notCol H G A).
-------------apply (@euclidean__tactics.nCol__not__Col H G A).
--------------apply (@lemma__equalanglesNC.lemma__equalanglesNC G H D H G A H24).


------------ assert (* Cut *) (euclidean__defs.CongA H G A A G H) as H26.
------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA H G A H25).
------------- assert (* Cut *) (euclidean__defs.CongA G H D A G H) as H27.
-------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive G H D H G A A G H H24 H26).
-------------- assert (* Cut *) (euclidean__defs.CongA A G H G H D) as H28.
--------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric G H D A G H H27).
--------------- assert (* Cut *) (G = G) as H29.
---------------- apply (@logic.eq__refl Point G).
---------------- assert (* Cut *) (euclidean__axioms.Col G H G) as H30.
----------------- right.
left.
exact H29.
----------------- assert (* Cut *) (euclidean__axioms.nCol A G H) as H31.
------------------ apply (@euclidean__tactics.nCol__notCol A G H).
-------------------apply (@euclidean__tactics.nCol__not__Col A G H).
--------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC G H D A G H H27).


------------------ assert (* Cut *) (~(euclidean__axioms.Col G H A)) as H32.
------------------- intro H32.
assert (* Cut *) (euclidean__axioms.Col A G H) as H33.
-------------------- assert (* Cut *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H33.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder G H A H32).
--------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H38.
-------------------- apply (@euclidean__tactics.Col__nCol__False A G H H31 H33).
------------------- assert (* Cut *) (euclidean__axioms.TS A G H B) as H33.
-------------------- exists G.
split.
--------------------- exact H0.
--------------------- split.
---------------------- exact H30.
---------------------- apply (@euclidean__tactics.nCol__notCol G H A H32).
-------------------- assert (* Cut *) (euclidean__axioms.TS B G H A) as H34.
--------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H A B H33).
--------------------- assert (* Cut *) (euclidean__axioms.TS D G H A) as H35.
---------------------- apply (@lemma__planeseparation.lemma__planeseparation G H D B A H4 H34).
---------------------- assert (* Cut *) (euclidean__axioms.TS A G H D) as H36.
----------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H D A H35).
----------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H37.
------------------------ apply (@proposition__27.proposition__27 A B C D G H H0 H1 H28 H36).
------------------------ exact H37.
Qed.
