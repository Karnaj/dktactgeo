Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__TGflip.
Require Export lemma__TGsymmetric.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__20.
Require Export proposition__22.
Definition proposition__23 : forall A B C D E, (euclidean__axioms.neq A B) -> ((euclidean__axioms.nCol D C E) -> (exists X Y, (euclidean__defs.Out A B Y) /\ (euclidean__defs.CongA X A Y D C E))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (~(euclidean__axioms.Col E C D)) as H1.
- intro H1.
assert (* Cut *) (euclidean__axioms.Col D C E) as H2.
-- assert (* Cut *) ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col E D C) /\ (euclidean__axioms.Col D C E))))) as H2.
--- apply (@lemma__collinearorder.lemma__collinearorder E C D H1).
--- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H10.
-- apply (@euclidean__tactics.Col__nCol__False D C E H0 H2).
- assert (* Cut *) (~(euclidean__axioms.Col C E D)) as H2.
-- intro H2.
assert (* Cut *) (euclidean__axioms.Col D C E) as H3.
--- assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H3.
---- apply (@lemma__collinearorder.lemma__collinearorder C E D H2).
---- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H8.
--- apply (@H1).
----apply (@euclidean__tactics.not__nCol__Col E C D).
-----intro H4.
apply (@euclidean__tactics.Col__nCol__False D C E H0 H3).


-- assert (euclidean__axioms.Triangle D C E) as H3 by exact H0.
assert (* Cut *) (euclidean__axioms.Triangle C E D) as H4.
--- apply (@euclidean__tactics.nCol__notCol C E D H2).
--- assert (* Cut *) (euclidean__axioms.Triangle E C D) as H5.
---- apply (@euclidean__tactics.nCol__notCol E C D H1).
---- assert (* Cut *) (euclidean__defs.TG C D D E C E) as H6.
----- apply (@proposition__20.proposition__20 D C E H3).
----- assert (* Cut *) (euclidean__defs.TG C E E D C D) as H7.
------ apply (@proposition__20.proposition__20 E C D H5).
------ assert (* Cut *) (euclidean__defs.TG E C C D E D) as H8.
------- apply (@proposition__20.proposition__20 C E D H4).
------- assert (* Cut *) (euclidean__defs.TG C D E C E D) as H9.
-------- apply (@lemma__TGsymmetric.lemma__TGsymmetric E C E C D D H8).
-------- assert (* Cut *) (euclidean__defs.TG C D D E E C) as H10.
--------- assert (* Cut *) ((euclidean__defs.TG D C D E C E) /\ (euclidean__defs.TG C D D E E C)) as H10.
---------- apply (@lemma__TGflip.lemma__TGflip C D C D E E H6).
---------- destruct H10 as [H11 H12].
exact H12.
--------- assert (* Cut *) (euclidean__defs.TG D E C D E C) as H11.
---------- apply (@lemma__TGsymmetric.lemma__TGsymmetric C D E D E C H10).
---------- assert (* Cut *) (euclidean__defs.TG E D C D E C) as H12.
----------- assert (* Cut *) ((euclidean__defs.TG E D C D E C) /\ (euclidean__defs.TG D E C D C E)) as H12.
------------ apply (@lemma__TGflip.lemma__TGflip D C E E D C H11).
------------ destruct H12 as [H13 H14].
exact H13.
----------- assert (* Cut *) (euclidean__defs.TG C D E D E C) as H13.
------------ apply (@lemma__TGsymmetric.lemma__TGsymmetric E C E D D C H12).
------------ assert (* Cut *) (euclidean__defs.TG E C E D C D) as H14.
------------- assert (* Cut *) ((euclidean__defs.TG E C E D C D) /\ (euclidean__defs.TG C E E D D C)) as H14.
-------------- apply (@lemma__TGflip.lemma__TGflip C E C E D D H7).
-------------- destruct H14 as [H15 H16].
exact H15.
------------- assert (* Cut *) (exists G F, (euclidean__axioms.Cong A G E C) /\ ((euclidean__axioms.Cong A F C D) /\ ((euclidean__axioms.Cong G F E D) /\ ((euclidean__defs.Out A B G) /\ (euclidean__axioms.Triangle A G F))))) as H15.
-------------- apply (@proposition__22.proposition__22 C E E B A D C D H9 H13 H14 H).
-------------- destruct H15 as [G H16].
destruct H16 as [F H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Cong A G C E) as H26.
--------------- assert (* Cut *) ((euclidean__axioms.Cong G A C E) /\ ((euclidean__axioms.Cong G A E C) /\ (euclidean__axioms.Cong A G C E))) as H26.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip A G E C H18).
---------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H30.
--------------- assert (* Cut *) (euclidean__axioms.Cong F G D E) as H27.
---------------- assert (* Cut *) ((euclidean__axioms.Cong F G D E) /\ ((euclidean__axioms.Cong F G E D) /\ (euclidean__axioms.Cong G F D E))) as H27.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip G F E D H22).
----------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H28.
---------------- assert (* Cut *) (E = E) as H28.
----------------- apply (@logic.eq__refl Point E).
----------------- assert (* Cut *) (D = D) as H29.
------------------ apply (@logic.eq__refl Point D).
------------------ assert (* Cut *) (F = F) as H30.
------------------- apply (@logic.eq__refl Point F).
------------------- assert (* Cut *) (G = G) as H31.
-------------------- apply (@logic.eq__refl Point G).
-------------------- assert (* Cut *) (~(C = E)) as H32.
--------------------- intro H32.
assert (* Cut *) (euclidean__axioms.Col D C E) as H33.
---------------------- right.
right.
left.
exact H32.
---------------------- apply (@H1).
-----------------------apply (@euclidean__tactics.not__nCol__Col E C D).
------------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False D C E H3 H33).


--------------------- assert (* Cut *) (~(C = D)) as H33.
---------------------- intro H33.
assert (* Cut *) (euclidean__axioms.Col C D E) as H34.
----------------------- left.
exact H33.
----------------------- assert (* Cut *) (euclidean__axioms.Col D C E) as H35.
------------------------ assert (* Cut *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col C E D) /\ (euclidean__axioms.Col E D C))))) as H35.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D E H34).
------------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H36.
------------------------ apply (@H1).
-------------------------apply (@euclidean__tactics.not__nCol__Col E C D).
--------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False D C E H3 H35).


---------------------- assert (* Cut *) (euclidean__defs.Out C E E) as H34.
----------------------- apply (@lemma__ray4.lemma__ray4 C E E).
------------------------right.
left.
exact H28.

------------------------ exact H32.
----------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H35.
------------------------ apply (@lemma__ray4.lemma__ray4 C D D).
-------------------------right.
left.
exact H29.

------------------------- exact H33.
------------------------ assert (* Cut *) (~(euclidean__axioms.Col F A G)) as H36.
------------------------- intro H36.
assert (* Cut *) (euclidean__axioms.Col A G F) as H37.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col A F G) /\ ((euclidean__axioms.Col A G F) /\ ((euclidean__axioms.Col G F A) /\ ((euclidean__axioms.Col F G A) /\ (euclidean__axioms.Col G A F))))) as H37.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A G H36).
--------------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H40.
-------------------------- assert (euclidean__axioms.nCol A G F) as H38 by exact H25.
apply (@H1).
---------------------------apply (@euclidean__tactics.not__nCol__Col E C D).
----------------------------intro H39.
apply (@euclidean__tactics.Col__nCol__False A G F H38 H37).


------------------------- assert (* Cut *) (~(A = F)) as H37.
-------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.Col A F G) as H38.
--------------------------- left.
exact H37.
--------------------------- assert (* Cut *) (euclidean__axioms.Col F A G) as H39.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col F A G) /\ ((euclidean__axioms.Col F G A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A G F) /\ (euclidean__axioms.Col G F A))))) as H39.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F G H38).
----------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H40.
---------------------------- apply (@H1).
-----------------------------apply (@euclidean__tactics.not__nCol__Col E C D).
------------------------------intro H40.
apply (@H36 H39).


-------------------------- assert (* Cut *) (euclidean__defs.Out A F F) as H38.
--------------------------- apply (@lemma__ray4.lemma__ray4 A F F).
----------------------------right.
left.
exact H30.

---------------------------- exact H37.
--------------------------- assert (* Cut *) (~(A = G)) as H39.
---------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.Col A G F) as H40.
----------------------------- left.
exact H39.
----------------------------- assert (* Cut *) (euclidean__axioms.Col F A G) as H41.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col G F A) /\ ((euclidean__axioms.Col F A G) /\ ((euclidean__axioms.Col A F G) /\ (euclidean__axioms.Col F G A))))) as H41.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A G F H40).
------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
------------------------------ apply (@H1).
-------------------------------apply (@euclidean__tactics.not__nCol__Col E C D).
--------------------------------intro H42.
apply (@H36 H41).


---------------------------- assert (* Cut *) (euclidean__defs.Out A G G) as H40.
----------------------------- apply (@lemma__ray4.lemma__ray4 A G G).
------------------------------right.
left.
exact H31.

------------------------------ exact H39.
----------------------------- assert (* Cut *) (euclidean__defs.CongA F A G D C E) as H41.
------------------------------ exists F.
exists G.
exists D.
exists E.
split.
------------------------------- exact H38.
------------------------------- split.
-------------------------------- exact H40.
-------------------------------- split.
--------------------------------- exact H35.
--------------------------------- split.
---------------------------------- exact H34.
---------------------------------- split.
----------------------------------- exact H20.
----------------------------------- split.
------------------------------------ exact H26.
------------------------------------ split.
------------------------------------- exact H27.
------------------------------------- apply (@euclidean__tactics.nCol__notCol F A G H36).
------------------------------ exists F.
exists G.
split.
------------------------------- exact H24.
------------------------------- exact H41.
Qed.
