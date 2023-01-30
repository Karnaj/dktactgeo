Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__15.
Require Export proposition__27.
Definition proposition__28A : forall A B C D E G H, (euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS C H D) -> ((euclidean__axioms.BetS E G H) -> ((euclidean__defs.CongA E G B G H D) -> ((euclidean__defs.OS B D G H) -> (euclidean__defs.Par A B C D))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (euclidean__defs.OS D B G H) as H5.
- assert (* Cut *) ((euclidean__defs.OS D B G H) /\ ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G))) as H5.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric G H B D H4).
-- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H6.
- assert (* Cut *) (euclidean__axioms.nCol E G B) as H6.
-- assert (exists U V u v, (euclidean__defs.Out G E U) /\ ((euclidean__defs.Out G B V) /\ ((euclidean__defs.Out H G u) /\ ((euclidean__defs.Out H D v) /\ ((euclidean__axioms.Cong G U H u) /\ ((euclidean__axioms.Cong G V H v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E G B)))))))) as H6 by exact H3.
assert (exists U V u v, (euclidean__defs.Out G E U) /\ ((euclidean__defs.Out G B V) /\ ((euclidean__defs.Out H G u) /\ ((euclidean__defs.Out H D v) /\ ((euclidean__axioms.Cong G U H u) /\ ((euclidean__axioms.Cong G V H v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E G B)))))))) as __TmpHyp by exact H6.
destruct __TmpHyp as [x H7].
destruct H7 as [x0 H8].
destruct H8 as [x1 H9].
destruct H9 as [x2 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H24.
-- assert (* Cut *) (G = G) as H7.
--- apply (@logic.eq__refl Point G).
--- assert (* Cut *) (euclidean__axioms.Col G H G) as H8.
---- right.
left.
exact H7.
---- assert (* Cut *) (~(euclidean__axioms.Col G H A)) as H9.
----- intro H9.
assert (* Cut *) (euclidean__axioms.Col H G A) as H10.
------ assert (* Cut *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H10.
------- apply (@lemma__collinearorder.lemma__collinearorder G H A H9).
------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H11.
------ assert (* Cut *) (euclidean__axioms.Col E G H) as H11.
------- right.
right.
right.
right.
left.
exact H2.
------- assert (* Cut *) (euclidean__axioms.Col H G E) as H12.
-------- assert (* Cut *) ((euclidean__axioms.Col G E H) /\ ((euclidean__axioms.Col G H E) /\ ((euclidean__axioms.Col H E G) /\ ((euclidean__axioms.Col E H G) /\ (euclidean__axioms.Col H G E))))) as H12.
--------- apply (@lemma__collinearorder.lemma__collinearorder E G H H11).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
-------- assert (* Cut *) (euclidean__axioms.neq G H) as H13.
--------- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E H))) as H13.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal E G H H2).
---------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.neq H G) as H14.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G H H13).
---------- assert (* Cut *) (euclidean__axioms.Col G A E) as H15.
----------- apply (@euclidean__tactics.not__nCol__Col G A E).
------------intro H15.
apply (@euclidean__tactics.Col__nCol__False G A E H15).
-------------apply (@lemma__collinear4.lemma__collinear4 H G A E H10 H12 H14).


----------- assert (* Cut *) (euclidean__axioms.Col A G E) as H16.
------------ assert (* Cut *) ((euclidean__axioms.Col A G E) /\ ((euclidean__axioms.Col A E G) /\ ((euclidean__axioms.Col E G A) /\ ((euclidean__axioms.Col G E A) /\ (euclidean__axioms.Col E A G))))) as H16.
------------- apply (@lemma__collinearorder.lemma__collinearorder G A E H15).
------------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H17.
------------ assert (* Cut *) (euclidean__axioms.Col A G B) as H17.
------------- right.
right.
right.
right.
left.
exact H0.
------------- assert (* Cut *) (euclidean__axioms.neq A G) as H18.
-------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H18.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H0).
--------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H21.
-------------- assert (* Cut *) (euclidean__axioms.Col G E B) as H19.
--------------- apply (@euclidean__tactics.not__nCol__Col G E B).
----------------intro H19.
apply (@euclidean__tactics.Col__nCol__False G E B H19).
-----------------apply (@lemma__collinear4.lemma__collinear4 A G E B H16 H17 H18).


--------------- assert (* Cut *) (euclidean__axioms.Col E G B) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.Col E G B) /\ ((euclidean__axioms.Col E B G) /\ ((euclidean__axioms.Col B G E) /\ ((euclidean__axioms.Col G B E) /\ (euclidean__axioms.Col B E G))))) as H20.
----------------- apply (@lemma__collinearorder.lemma__collinearorder G E B H19).
----------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
---------------- apply (@euclidean__tactics.Col__nCol__False E G B H6 H20).
----- assert (* Cut *) (euclidean__axioms.TS A G H B) as H10.
------ exists G.
split.
------- exact H0.
------- split.
-------- exact H8.
-------- apply (@euclidean__tactics.nCol__notCol G H A H9).
------ assert (* Cut *) (euclidean__axioms.TS B G H A) as H11.
------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H A B H10).
------- assert (* Cut *) (euclidean__axioms.BetS B G A) as H12.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry A G B H0).
-------- assert (* Cut *) (euclidean__defs.CongA E G B A G H) as H13.
--------- apply (@proposition__15.proposition__15a E H B A G H2 H12 H6).
--------- assert (* Cut *) (euclidean__defs.CongA A G H E G B) as H14.
---------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric E G B A G H H13).
---------- assert (* Cut *) (euclidean__defs.CongA A G H G H D) as H15.
----------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A G H E G B G H D H14 H3).
----------- assert (* Cut *) (euclidean__axioms.TS D G H A) as H16.
------------ apply (@lemma__planeseparation.lemma__planeseparation G H D B A H5 H11).
------------ assert (* Cut *) (euclidean__axioms.TS A G H D) as H17.
------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H D A H16).
------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H18.
-------------- apply (@proposition__27.proposition__27 A B C D G H H0 H1 H15 H17).
-------------- exact H18.
Qed.
