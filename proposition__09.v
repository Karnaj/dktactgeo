Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__doublereverse.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__ray4.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__10.
Definition proposition__09 : forall A B C, (euclidean__axioms.nCol B A C) -> (exists X, (euclidean__defs.CongA B A X X A C) /\ (euclidean__defs.InAngle B A C X)).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(A = B)) as H0.
- intro H0.
assert (* Cut *) (B = A) as H1.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric B A H0).
-- assert (* Cut *) (euclidean__axioms.Col B A C) as H2.
--- left.
exact H1.
--- apply (@euclidean__tactics.Col__nCol__False B A C H H2).
- assert (* Cut *) (~(A = C)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col B A C) as H2.
--- right.
right.
left.
exact H1.
--- apply (@euclidean__tactics.Col__nCol__False B A C H H2).
-- assert (* Cut *) (exists E, (euclidean__defs.Out A C E) /\ (euclidean__axioms.Cong A E A B)) as H2.
--- apply (@lemma__layoff.lemma__layoff A C A B H1 H0).
--- destruct H2 as [E H3].
destruct H3 as [H4 H5].
assert (* Cut *) (~(B = E)) as H6.
---- intro H6.
assert (* Cut *) (euclidean__axioms.Col A B E) as H7.
----- right.
right.
left.
exact H6.
----- assert (* Cut *) (euclidean__axioms.Col A C E) as H8.
------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A C E H4).
------ assert (* Cut *) (euclidean__axioms.Col E A B) as H9.
------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H9.
-------- apply (@lemma__collinearorder.lemma__collinearorder A B E H7).
-------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.Col E A C) as H10.
-------- assert (* Cut *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col A E C) /\ (euclidean__axioms.Col E C A))))) as H10.
--------- apply (@lemma__collinearorder.lemma__collinearorder A C E H8).
--------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
-------- assert (* Cut *) (euclidean__axioms.neq A E) as H11.
--------- apply (@eq__ind__r euclidean__axioms.Point E (fun B0 => (euclidean__axioms.nCol B0 A C) -> ((~(A = B0)) -> ((euclidean__axioms.Cong A E A B0) -> ((euclidean__axioms.Col A B0 E) -> ((euclidean__axioms.Col E A B0) -> (euclidean__axioms.neq A E))))))) with (x := B).
----------intro H11.
intro H12.
intro H13.
intro H14.
intro H15.
exact H12.

---------- exact H6.
---------- exact H.
---------- exact H0.
---------- exact H5.
---------- exact H7.
---------- exact H9.
--------- assert (* Cut *) (euclidean__axioms.neq E A) as H12.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H11).
---------- assert (* Cut *) (euclidean__axioms.Col A B C) as H13.
----------- apply (@euclidean__tactics.not__nCol__Col A B C).
------------intro H13.
apply (@euclidean__tactics.Col__nCol__False A B C H13).
-------------apply (@lemma__collinear4.lemma__collinear4 E A B C H9 H10 H12).


----------- assert (* Cut *) (euclidean__axioms.Col B A C) as H14.
------------ assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H14.
------------- apply (@lemma__collinearorder.lemma__collinearorder A B C H13).
------------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H15.
------------ apply (@euclidean__tactics.Col__nCol__False B A C H H14).
---- assert (* Cut *) (exists F, (euclidean__axioms.BetS B F E) /\ (euclidean__axioms.Cong F B F E)) as H7.
----- apply (@proposition__10.proposition__10 B E H6).
----- destruct H7 as [F H8].
destruct H8 as [H9 H10].
assert (* Cut *) (B = B) as H11.
------ apply (@logic.eq__refl Point B).
------ assert (* Cut *) (F = F) as H12.
------- apply (@logic.eq__refl Point F).
------- assert (* Cut *) (euclidean__axioms.Cong A F A F) as H13.
-------- apply (@euclidean__axioms.cn__congruencereflexive A F).
-------- assert (* Cut *) (euclidean__axioms.Cong A B A E) as H14.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A E B H5).
--------- assert (* Cut *) (euclidean__axioms.Cong E F B F) as H15.
---------- assert (* Cut *) ((euclidean__axioms.Cong E F B F) /\ (euclidean__axioms.Cong B F E F)) as H15.
----------- apply (@lemma__doublereverse.lemma__doublereverse F B F E H10).
----------- destruct H15 as [H16 H17].
exact H16.
---------- assert (* Cut *) (euclidean__axioms.Cong B F E F) as H16.
----------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B E F F H15).
----------- assert (* Cut *) (~(euclidean__axioms.Col B A F)) as H17.
------------ intro H17.
assert (* Cut *) (euclidean__axioms.Col B F E) as H18.
------------- right.
right.
right.
right.
left.
exact H9.
------------- assert (* Cut *) (euclidean__axioms.Col F B E) as H19.
-------------- assert (* Cut *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col B E F) /\ (euclidean__axioms.Col E F B))))) as H19.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B F E H18).
--------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H20.
-------------- assert (* Cut *) (euclidean__axioms.Col F B A) as H20.
--------------- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H20.
---------------- apply (@lemma__collinearorder.lemma__collinearorder B A F H17).
---------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
--------------- assert (* Cut *) (euclidean__axioms.neq B F) as H21.
---------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B E))) as H21.
----------------- apply (@lemma__betweennotequal.lemma__betweennotequal B F E H9).
----------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
---------------- assert (* Cut *) (euclidean__axioms.neq F B) as H22.
----------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B F H21).
----------------- assert (* Cut *) (euclidean__axioms.Col B E A) as H23.
------------------ apply (@euclidean__tactics.not__nCol__Col B E A).
-------------------intro H23.
apply (@euclidean__tactics.Col__nCol__False B E A H23).
--------------------apply (@lemma__collinear4.lemma__collinear4 F B E A H19 H20 H22).


------------------ assert (* Cut *) (euclidean__axioms.Col A C E) as H24.
------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A C E H4).
------------------- assert (* Cut *) (euclidean__axioms.Col E A B) as H25.
-------------------- assert (* Cut *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B A E) /\ (euclidean__axioms.Col A E B))))) as H25.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder B E A H23).
--------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H28.
-------------------- assert (* Cut *) (euclidean__axioms.Col E A C) as H26.
--------------------- assert (* Cut *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col C E A) /\ ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col A E C) /\ (euclidean__axioms.Col E C A))))) as H26.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder A C E H24).
---------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H31.
--------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H27.
---------------------- apply (@lemma__raystrict.lemma__raystrict A C E H4).
---------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H28.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H27).
----------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H29.
------------------------ apply (@euclidean__tactics.not__nCol__Col A B C).
-------------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False A B C H29).
--------------------------apply (@lemma__collinear4.lemma__collinear4 E A B C H25 H26 H28).


------------------------ assert (* Cut *) (euclidean__axioms.Col B A C) as H30.
------------------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H30.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B C H29).
-------------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H31.
------------------------- apply (@euclidean__tactics.Col__nCol__False B A C H H30).
------------ assert (* Cut *) (euclidean__defs.Out A B B) as H18.
------------- apply (@lemma__ray4.lemma__ray4 A B B).
--------------right.
left.
exact H11.

-------------- exact H0.
------------- assert (* Cut *) (~(A = F)) as H19.
-------------- intro H19.
assert (* Cut *) (euclidean__axioms.Col B A F) as H20.
--------------- right.
right.
left.
exact H19.
--------------- apply (@H17 H20).
-------------- assert (* Cut *) (euclidean__defs.Out A F F) as H20.
--------------- apply (@lemma__ray4.lemma__ray4 A F F).
----------------right.
left.
exact H12.

---------------- exact H19.
--------------- assert (* Cut *) (euclidean__defs.CongA B A F C A F) as H21.
---------------- exists B.
exists F.
exists E.
exists F.
split.
----------------- exact H18.
----------------- split.
------------------ exact H20.
------------------ split.
------------------- exact H4.
------------------- split.
-------------------- exact H20.
-------------------- split.
--------------------- exact H14.
--------------------- split.
---------------------- exact H13.
---------------------- split.
----------------------- exact H16.
----------------------- apply (@euclidean__tactics.nCol__notCol B A F H17).
---------------- assert (* Cut *) (euclidean__defs.CongA C A F B A F) as H22.
----------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B A F C A F H21).
----------------- assert (* Cut *) (euclidean__axioms.nCol C A F) as H23.
------------------ assert (exists U V u v, (euclidean__defs.Out A C U) /\ ((euclidean__defs.Out A F V) /\ ((euclidean__defs.Out A B u) /\ ((euclidean__defs.Out A F v) /\ ((euclidean__axioms.Cong A U A u) /\ ((euclidean__axioms.Cong A V A v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol C A F)))))))) as H23 by exact H22.
assert (exists U V u v, (euclidean__defs.Out A C U) /\ ((euclidean__defs.Out A F V) /\ ((euclidean__defs.Out A B u) /\ ((euclidean__defs.Out A F v) /\ ((euclidean__axioms.Cong A U A u) /\ ((euclidean__axioms.Cong A V A v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol C A F)))))))) as __TmpHyp by exact H23.
destruct __TmpHyp as [x H24].
destruct H24 as [x0 H25].
destruct H25 as [x1 H26].
destruct H26 as [x2 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
assert (exists U V u v, (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A F V) /\ ((euclidean__defs.Out A C u) /\ ((euclidean__defs.Out A F v) /\ ((euclidean__axioms.Cong A U A u) /\ ((euclidean__axioms.Cong A V A v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A F)))))))) as H42 by exact H21.
assert (exists U V u v, (euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A F V) /\ ((euclidean__defs.Out A C u) /\ ((euclidean__defs.Out A F v) /\ ((euclidean__axioms.Cong A U A u) /\ ((euclidean__axioms.Cong A V A v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B A F)))))))) as __TmpHyp0 by exact H42.
destruct __TmpHyp0 as [x3 H43].
destruct H43 as [x4 H44].
destruct H44 as [x5 H45].
destruct H45 as [x6 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H41.
------------------ assert (* Cut *) (euclidean__defs.CongA C A F F A C) as H24.
------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C A F H23).
------------------- assert (* Cut *) (euclidean__defs.CongA B A F F A C) as H25.
-------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B A F C A F F A C H21 H24).
-------------------- assert (* Cut *) (euclidean__defs.InAngle B A C F) as H26.
--------------------- exists B.
exists E.
split.
---------------------- exact H18.
---------------------- split.
----------------------- exact H4.
----------------------- exact H9.
--------------------- exists F.
split.
---------------------- exact H25.
---------------------- exact H26.
Qed.
