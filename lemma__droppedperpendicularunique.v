Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7a.
Require Export lemma__3__7b.
Require Export lemma__altitudebisectsbase.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__midpointunique.
Require Export lemma__rightreverse.
Require Export logic.
Definition lemma__droppedperpendicularunique : forall A J M P, (euclidean__defs.Per A M P) -> ((euclidean__defs.Per A J P) -> ((euclidean__axioms.Col A M J) -> (M = J))).
Proof.
intro A.
intro J.
intro M.
intro P.
intro H.
intro H0.
intro H1.
assert (* Cut *) (~(euclidean__axioms.neq M J)) as H2.
- intro H2.
assert (* Cut *) (euclidean__axioms.neq J M) as H3.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M J H2).
-- assert (* Cut *) (exists E, (euclidean__axioms.BetS M J E) /\ (euclidean__axioms.Cong J E M J)) as H4.
--- apply (@lemma__extension.lemma__extension M J M J H2 H2).
--- destruct H4 as [E H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.neq M E) as H8.
---- assert (* Cut *) ((euclidean__axioms.neq J E) /\ ((euclidean__axioms.neq M J) /\ (euclidean__axioms.neq M E))) as H8.
----- apply (@lemma__betweennotequal.lemma__betweennotequal M J E H6).
----- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H12.
---- assert (* Cut *) (exists F, (euclidean__axioms.BetS J M F) /\ (euclidean__axioms.Cong M F M E)) as H9.
----- apply (@lemma__extension.lemma__extension J M M E H3 H8).
----- destruct H9 as [F H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__axioms.BetS E J M) as H13.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry M J E H6).
------ assert (* Cut *) (euclidean__axioms.BetS E J F) as H14.
------- apply (@lemma__3__7b.lemma__3__7b E J M F H13 H11).
------- assert (* Cut *) (euclidean__axioms.BetS F J E) as H15.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry E J F H14).
-------- assert (* Cut *) (euclidean__axioms.BetS E M F) as H16.
--------- apply (@lemma__3__7a.lemma__3__7a E J M F H13 H11).
--------- assert (* Cut *) (euclidean__axioms.neq J F) as H17.
---------- assert (* Cut *) ((euclidean__axioms.neq J F) /\ ((euclidean__axioms.neq E J) /\ (euclidean__axioms.neq E F))) as H17.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal E J F H14).
----------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
---------- assert (* Cut *) (euclidean__axioms.neq F J) as H18.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric J F H17).
----------- assert (* Cut *) (euclidean__axioms.Col J M F) as H19.
------------ right.
right.
right.
right.
left.
exact H11.
------------ assert (* Cut *) (euclidean__axioms.Col M J F) as H20.
------------- assert (* Cut *) ((euclidean__axioms.Col M J F) /\ ((euclidean__axioms.Col M F J) /\ ((euclidean__axioms.Col F J M) /\ ((euclidean__axioms.Col J F M) /\ (euclidean__axioms.Col F M J))))) as H20.
-------------- apply (@lemma__collinearorder.lemma__collinearorder J M F H19).
-------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
------------- assert (* Cut *) (euclidean__axioms.Col M J A) as H21.
-------------- assert (* Cut *) ((euclidean__axioms.Col M A J) /\ ((euclidean__axioms.Col M J A) /\ ((euclidean__axioms.Col J A M) /\ ((euclidean__axioms.Col A J M) /\ (euclidean__axioms.Col J M A))))) as H21.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A M J H1).
--------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H24.
-------------- assert (* Cut *) (euclidean__axioms.neq J M) as H22.
--------------- assert (* Cut *) ((euclidean__axioms.neq M F) /\ ((euclidean__axioms.neq E M) /\ (euclidean__axioms.neq E F))) as H22.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal E M F H16).
---------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H3.
--------------- assert (euclidean__axioms.neq M J) as H23 by exact H2.
assert (* Cut *) (euclidean__axioms.Col J F A) as H24.
---------------- apply (@euclidean__tactics.not__nCol__Col J F A).
-----------------intro H24.
apply (@euclidean__tactics.Col__nCol__False J F A H24).
------------------apply (@lemma__collinear4.lemma__collinear4 M J F A H20 H21 H23).


---------------- assert (* Cut *) (euclidean__axioms.Col A J F) as H25.
----------------- assert (* Cut *) ((euclidean__axioms.Col F J A) /\ ((euclidean__axioms.Col F A J) /\ ((euclidean__axioms.Col A J F) /\ ((euclidean__axioms.Col J A F) /\ (euclidean__axioms.Col A F J))))) as H25.
------------------ apply (@lemma__collinearorder.lemma__collinearorder J F A H24).
------------------ destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
----------------- assert (* Cut *) (euclidean__defs.Per F J P) as H26.
------------------ apply (@lemma__collinearright.lemma__collinearright A J F P H0 H25 H18).
------------------ assert (euclidean__axioms.Col J M F) as H27 by exact H19.
assert (* Cut *) (euclidean__axioms.Col J M A) as H28.
------------------- assert (* Cut *) ((euclidean__axioms.Col J M A) /\ ((euclidean__axioms.Col J A M) /\ ((euclidean__axioms.Col A M J) /\ ((euclidean__axioms.Col M A J) /\ (euclidean__axioms.Col A J M))))) as H28.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder M J A H21).
-------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H29.
------------------- assert (* Cut *) (euclidean__axioms.Col M F A) as H29.
-------------------- apply (@euclidean__tactics.not__nCol__Col M F A).
---------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False M F A H29).
----------------------apply (@lemma__collinear4.lemma__collinear4 J M F A H27 H28 H22).


-------------------- assert (* Cut *) (euclidean__axioms.Col A M F) as H30.
--------------------- assert (* Cut *) ((euclidean__axioms.Col F M A) /\ ((euclidean__axioms.Col F A M) /\ ((euclidean__axioms.Col A M F) /\ ((euclidean__axioms.Col M A F) /\ (euclidean__axioms.Col A F M))))) as H30.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder M F A H29).
---------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
--------------------- assert (* Cut *) (euclidean__axioms.neq M F) as H31.
---------------------- assert (* Cut *) ((euclidean__axioms.neq M F) /\ ((euclidean__axioms.neq E M) /\ (euclidean__axioms.neq E F))) as H31.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E M F H16).
----------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H32.
---------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H32.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M F H31).
----------------------- assert (* Cut *) (euclidean__defs.Per F M P) as H33.
------------------------ apply (@lemma__collinearright.lemma__collinearright A M F P H H30 H32).
------------------------ assert (* Cut *) (euclidean__axioms.Cong F M M E) as H34.
------------------------- assert (* Cut *) ((euclidean__axioms.Cong F M E M) /\ ((euclidean__axioms.Cong F M M E) /\ (euclidean__axioms.Cong M F E M))) as H34.
-------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M F M E H12).
-------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
------------------------- assert (euclidean__defs.Per F M P) as H35 by exact H33.
assert (* Cut *) (euclidean__axioms.BetS F M E) as H36.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E M F H16).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong F P E P) as H37.
--------------------------- apply (@lemma__rightreverse.lemma__rightreverse F M P E H35 H36 H34).
--------------------------- assert (* Cut *) (euclidean__defs.Midpoint F J E) as H38.
---------------------------- apply (@lemma__altitudebisectsbase.lemma__altitudebisectsbase F E J P H15 H37 H26).
---------------------------- assert (euclidean__axioms.BetS F M E) as H39 by exact H36.
assert (* Cut *) (euclidean__axioms.Cong F M M E) as H40.
----------------------------- assert (* Cut *) ((euclidean__axioms.Cong P F P E) /\ ((euclidean__axioms.Cong P F E P) /\ (euclidean__axioms.Cong F P P E))) as H40.
------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip F P E P H37).
------------------------------ destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H34.
----------------------------- assert (* Cut *) (euclidean__defs.Midpoint F M E) as H41.
------------------------------ split.
------------------------------- exact H39.
------------------------------- exact H40.
------------------------------ assert (* Cut *) (J = M) as H42.
------------------------------- apply (@lemma__midpointunique.lemma__midpointunique F J E M H38 H41).
------------------------------- apply (@H3 H42).
- apply (@euclidean__tactics.NNPP (M = J)).
--intro H3.
assert (* Cut *) (False) as H4.
--- apply (@H2 H3).
--- contradiction H4.

Qed.
