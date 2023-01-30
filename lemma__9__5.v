Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__9__5a.
Require Export lemma__9__5b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray1.
Require Export lemma__rayimpliescollinear.
Require Export logic.
Definition lemma__9__5 : forall A B C P Q R, (euclidean__axioms.TS P A B C) -> ((euclidean__defs.Out R Q P) -> ((euclidean__axioms.Col A B R) -> (euclidean__axioms.TS Q A B C))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro Q.
intro R.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS R P Q) \/ ((Q = P) \/ (euclidean__axioms.BetS R Q P))) as H2.
- apply (@lemma__ray1.lemma__ray1 R Q P H0).
- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H3.
-- assert (* Cut *) ((euclidean__axioms.nCol C P R) \/ (euclidean__axioms.Col C P R)) as H3.
--- apply (@euclidean__tactics.nCol__or__Col C P R).
--- assert ((euclidean__axioms.nCol C P R) \/ (euclidean__axioms.Col C P R)) as H4 by exact H3.
assert ((euclidean__axioms.nCol C P R) \/ (euclidean__axioms.Col C P R)) as __TmpHyp by exact H4.
destruct __TmpHyp as [H5|H5].
---- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H6.
----- assert ((euclidean__axioms.BetS R P Q) \/ ((Q = P) \/ (euclidean__axioms.BetS R Q P))) as H6 by exact H2.
assert ((euclidean__axioms.BetS R P Q) \/ ((Q = P) \/ (euclidean__axioms.BetS R Q P))) as __TmpHyp0 by exact H6.
destruct __TmpHyp0 as [H7|H7].
------ assert (* Cut *) (~(euclidean__axioms.Col R Q C)) as H8.
------- intro H8.
assert (* Cut *) (euclidean__axioms.Col Q R C) as H9.
-------- assert (* Cut *) ((euclidean__axioms.Col Q R C) /\ ((euclidean__axioms.Col Q C R) /\ ((euclidean__axioms.Col C R Q) /\ ((euclidean__axioms.Col R C Q) /\ (euclidean__axioms.Col C Q R))))) as H9.
--------- apply (@lemma__collinearorder.lemma__collinearorder R Q C H8).
--------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H10.
-------- assert (* Cut *) (euclidean__axioms.Col R Q P) as H10.
--------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear R Q P H0).
--------- assert (* Cut *) (euclidean__axioms.Col Q R P) as H11.
---------- assert (* Cut *) ((euclidean__axioms.Col Q R P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P R Q) /\ ((euclidean__axioms.Col R P Q) /\ (euclidean__axioms.Col P Q R))))) as H11.
----------- apply (@lemma__collinearorder.lemma__collinearorder R Q P H10).
----------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H12.
---------- assert (* Cut *) (euclidean__axioms.neq R Q) as H12.
----------- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq R P) /\ (euclidean__axioms.neq R Q))) as H12.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal R P Q H7).
------------ destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H16.
----------- assert (* Cut *) (euclidean__axioms.neq Q R) as H13.
------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric R Q H12).
------------ assert (* Cut *) (euclidean__axioms.Col R C P) as H14.
------------- apply (@euclidean__tactics.not__nCol__Col R C P).
--------------intro H14.
apply (@euclidean__tactics.Col__nCol__False R C P H14).
---------------apply (@lemma__collinear4.lemma__collinear4 Q R C P H9 H11 H13).


------------- assert (* Cut *) (euclidean__axioms.Col C P R) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.Col C R P) /\ ((euclidean__axioms.Col C P R) /\ ((euclidean__axioms.Col P R C) /\ ((euclidean__axioms.Col R P C) /\ (euclidean__axioms.Col P C R))))) as H15.
--------------- apply (@lemma__collinearorder.lemma__collinearorder R C P H14).
--------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H18.
-------------- apply (@euclidean__tactics.Col__nCol__False C P R H5 H15).
------- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H9.
-------- apply (@lemma__9__5a.lemma__9__5a A B C P Q R H H7).
---------apply (@euclidean__tactics.nCol__notCol R Q C H8).

--------- exact H1.
-------- exact H9.
------ destruct H7 as [H8|H8].
------- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H9.
-------- apply (@eq__ind__r euclidean__axioms.Point P (fun Q0 => (euclidean__defs.Out R Q0 P) -> (euclidean__axioms.TS Q0 A B C))) with (x := Q).
---------intro H9.
exact H.

--------- exact H8.
--------- exact H0.
-------- exact H9.
------- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H9.
-------- apply (@lemma__9__5b.lemma__9__5b A B C P Q R H H8 H5 H1).
-------- exact H9.
----- exact H6.
---- assert (exists L, (euclidean__axioms.BetS P L C) /\ ((euclidean__axioms.Col A B L) /\ (euclidean__axioms.nCol A B P))) as H6 by exact H.
destruct H6 as [L H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Col R Q P) as H12.
----- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear R Q P H0).
----- assert (* Cut *) (euclidean__axioms.Col P C L) as H13.
------ right.
right.
right.
right.
right.
exact H8.
------ assert (* Cut *) (euclidean__axioms.Col C P L) as H14.
------- assert (* Cut *) ((euclidean__axioms.Col C P L) /\ ((euclidean__axioms.Col C L P) /\ ((euclidean__axioms.Col L P C) /\ ((euclidean__axioms.Col P L C) /\ (euclidean__axioms.Col L C P))))) as H14.
-------- apply (@lemma__collinearorder.lemma__collinearorder P C L H13).
-------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H15.
------- assert (* Cut *) (euclidean__axioms.neq P C) as H15.
-------- assert (* Cut *) ((euclidean__axioms.neq L C) /\ ((euclidean__axioms.neq P L) /\ (euclidean__axioms.neq P C))) as H15.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal P L C H8).
--------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H19.
-------- assert (* Cut *) (euclidean__axioms.neq C P) as H16.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P C H15).
--------- assert (* Cut *) (euclidean__axioms.Col P L R) as H17.
---------- apply (@euclidean__tactics.not__nCol__Col P L R).
-----------intro H17.
apply (@euclidean__tactics.Col__nCol__False P L R H17).
------------apply (@lemma__collinear4.lemma__collinear4 C P L R H14 H5 H16).


---------- assert (* Cut *) (~(A = B)) as H18.
----------- intro H18.
assert (* Cut *) (euclidean__axioms.Col A B P) as H19.
------------ left.
exact H18.
------------ apply (@euclidean__tactics.Col__nCol__False A B P H11 H19).
----------- assert (* Cut *) (euclidean__axioms.Col B L R) as H19.
------------ apply (@euclidean__tactics.not__nCol__Col B L R).
-------------intro H19.
apply (@euclidean__tactics.Col__nCol__False B L R H19).
--------------apply (@lemma__collinear4.lemma__collinear4 A B L R H10 H1 H18).


------------ assert (* Cut *) (euclidean__axioms.Col L R P) as H20.
------------- assert (* Cut *) ((euclidean__axioms.Col L P R) /\ ((euclidean__axioms.Col L R P) /\ ((euclidean__axioms.Col R P L) /\ ((euclidean__axioms.Col P R L) /\ (euclidean__axioms.Col R L P))))) as H20.
-------------- apply (@lemma__collinearorder.lemma__collinearorder P L R H17).
-------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H23.
------------- assert (* Cut *) (euclidean__axioms.Col L R B) as H21.
-------------- assert (* Cut *) ((euclidean__axioms.Col L B R) /\ ((euclidean__axioms.Col L R B) /\ ((euclidean__axioms.Col R B L) /\ ((euclidean__axioms.Col B R L) /\ (euclidean__axioms.Col R L B))))) as H21.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B L R H19).
--------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H24.
-------------- assert (* Cut *) (~(euclidean__axioms.neq L R)) as H22.
--------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col R P B) as H23.
---------------- apply (@euclidean__tactics.not__nCol__Col R P B).
-----------------intro H23.
apply (@euclidean__tactics.Col__nCol__False R P B H23).
------------------apply (@lemma__collinear4.lemma__collinear4 L R P B H20 H21 H22).


---------------- assert (* Cut *) (euclidean__axioms.Col R B P) as H24.
----------------- assert (* Cut *) ((euclidean__axioms.Col P R B) /\ ((euclidean__axioms.Col P B R) /\ ((euclidean__axioms.Col B R P) /\ ((euclidean__axioms.Col R B P) /\ (euclidean__axioms.Col B P R))))) as H24.
------------------ apply (@lemma__collinearorder.lemma__collinearorder R P B H23).
------------------ destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
----------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H25.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H25.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A B R H1).
------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H33.
------------------ assert (* Cut *) (~(euclidean__axioms.neq R B)) as H26.
------------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col B P A) as H27.
-------------------- apply (@euclidean__tactics.not__nCol__Col B P A).
---------------------intro H27.
apply (@euclidean__tactics.Col__nCol__False B P A H27).
----------------------apply (@lemma__collinear4.lemma__collinear4 R B P A H24 H25 H26).


-------------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H28.
--------------------- assert (* Cut *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))))) as H28.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B P A H27).
---------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H33.
--------------------- apply (@euclidean__tactics.Col__nCol__False A B P H11 H28).
------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H27.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H18).
-------------------- assert (* Cut *) (euclidean__axioms.neq R A) as H28.
--------------------- assert (* Cut *) (R = B) as H28.
---------------------- apply (@euclidean__tactics.NNPP (R = B) H26).
---------------------- intro H29.
assert (* Cut *) (A = B) as Heq.
----------------------- apply (@logic.eq__trans Point A R B).
------------------------apply (@logic.eq__sym Point R A H29).

------------------------ exact H28.
----------------------- assert False.
------------------------apply (@H18 Heq).
------------------------ contradiction.
--------------------- assert (* Cut *) (euclidean__axioms.Col B A R) as H29.
---------------------- assert (* Cut *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R))))) as H29.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder R B A H25).
----------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
---------------------- assert (* Cut *) (euclidean__axioms.Col B A L) as H30.
----------------------- assert (* Cut *) ((euclidean__axioms.Col B A L) /\ ((euclidean__axioms.Col B L A) /\ ((euclidean__axioms.Col L A B) /\ ((euclidean__axioms.Col A L B) /\ (euclidean__axioms.Col L B A))))) as H30.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder A B L H10).
------------------------ destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H31.
----------------------- assert (* Cut *) (euclidean__axioms.Col A L R) as H31.
------------------------ apply (@euclidean__tactics.not__nCol__Col A L R).
-------------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False A L R H31).
--------------------------apply (@lemma__collinear4.lemma__collinear4 B A L R H30 H29 H27).


------------------------ assert (* Cut *) (euclidean__axioms.Col L R A) as H32.
------------------------- assert (* Cut *) ((euclidean__axioms.Col L A R) /\ ((euclidean__axioms.Col L R A) /\ ((euclidean__axioms.Col R A L) /\ ((euclidean__axioms.Col A R L) /\ (euclidean__axioms.Col R L A))))) as H32.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder A L R H31).
-------------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H35.
------------------------- assert (* Cut *) (euclidean__axioms.Col R P A) as H33.
-------------------------- apply (@euclidean__tactics.not__nCol__Col R P A).
---------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False R P A H33).
----------------------------apply (@lemma__collinear4.lemma__collinear4 L R P A H20 H32 H22).


-------------------------- assert (* Cut *) (euclidean__axioms.Col R A P) as H34.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col P R A) /\ ((euclidean__axioms.Col P A R) /\ ((euclidean__axioms.Col A R P) /\ ((euclidean__axioms.Col R A P) /\ (euclidean__axioms.Col A P R))))) as H34.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder R P A H33).
---------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
--------------------------- assert (* Cut *) (euclidean__axioms.Col R A B) as H35.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H35.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A R H29).
----------------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H43.
---------------------------- assert (* Cut *) (euclidean__axioms.Col A P B) as H36.
----------------------------- apply (@euclidean__tactics.not__nCol__Col A P B).
------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False A P B H36).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 R A P B H34 H35 H28).


----------------------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H37.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))))) as H37.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A P B H36).
------------------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H44.
------------------------------ apply (@euclidean__tactics.Col__nCol__False A B P H11 H37).
--------------- assert (* Cut *) (euclidean__axioms.BetS P R C) as H23.
---------------- apply (@eq__ind euclidean__axioms.Point L (fun X => euclidean__axioms.BetS P X C)) with (y := R).
----------------- exact H8.
-----------------apply (@euclidean__tactics.NNPP (L = R) H22).

---------------- assert (* Cut *) (euclidean__axioms.BetS C R P) as H24.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry P R C H23).
----------------- assert (* Cut *) (euclidean__axioms.BetS C R Q) as H25.
------------------ assert ((euclidean__axioms.BetS R P Q) \/ ((Q = P) \/ (euclidean__axioms.BetS R Q P))) as H25 by exact H2.
assert ((euclidean__axioms.BetS R P Q) \/ ((Q = P) \/ (euclidean__axioms.BetS R Q P))) as __TmpHyp0 by exact H25.
destruct __TmpHyp0 as [H26|H26].
------------------- assert (* Cut *) (euclidean__axioms.BetS C R Q) as H27.
-------------------- apply (@lemma__3__7b.lemma__3__7b C R P Q H24 H26).
-------------------- exact H27.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (euclidean__axioms.BetS C R Q) as H28.
--------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun Q0 => (euclidean__defs.Out R Q0 P) -> ((euclidean__axioms.Col R Q0 P) -> (euclidean__axioms.BetS C R Q0)))) with (x := Q).
----------------------intro H28.
intro H29.
exact H24.

---------------------- exact H27.
---------------------- exact H0.
---------------------- exact H12.
--------------------- exact H28.
-------------------- assert (* Cut *) (euclidean__axioms.BetS C R Q) as H28.
--------------------- apply (@euclidean__axioms.axiom__innertransitivity C R Q P H24 H27).
--------------------- exact H28.
------------------ assert (* Cut *) (euclidean__axioms.BetS Q R C) as H26.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C R Q H25).
------------------- assert (* Cut *) (~(euclidean__axioms.Col A B Q)) as H27.
-------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col Q R C) as H28.
--------------------- right.
right.
right.
right.
left.
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.Col B Q R) as H29.
---------------------- apply (@euclidean__tactics.not__nCol__Col B Q R).
-----------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False B Q R H29).
------------------------apply (@lemma__collinear4.lemma__collinear4 A B Q R H27 H1 H18).


---------------------- assert (* Cut *) (euclidean__axioms.Col R B Q) as H30.
----------------------- assert (* Cut *) ((euclidean__axioms.Col Q B R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B R Q) /\ (euclidean__axioms.Col R Q B))))) as H30.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder B Q R H29).
------------------------ destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
----------------------- assert (euclidean__axioms.Col R Q P) as H31 by exact H12.
assert (* Cut *) (euclidean__axioms.Col Q R B) as H32.
------------------------ assert (* Cut *) ((euclidean__axioms.Col B R Q) /\ ((euclidean__axioms.Col B Q R) /\ ((euclidean__axioms.Col Q R B) /\ ((euclidean__axioms.Col R Q B) /\ (euclidean__axioms.Col Q B R))))) as H32.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder R B Q H30).
------------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H37.
------------------------ assert (* Cut *) (euclidean__axioms.Col Q R P) as H33.
------------------------- assert (* Cut *) ((euclidean__axioms.Col Q R P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P R Q) /\ ((euclidean__axioms.Col R P Q) /\ (euclidean__axioms.Col P Q R))))) as H33.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder R Q P H31).
-------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H34.
------------------------- assert (* Cut *) (euclidean__axioms.neq Q R) as H34.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq Q R) /\ (euclidean__axioms.neq Q C))) as H34.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q R C H26).
--------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
-------------------------- assert (* Cut *) (euclidean__axioms.Col R B P) as H35.
--------------------------- apply (@euclidean__tactics.not__nCol__Col R B P).
----------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False R B P H35).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 Q R B P H32 H33 H34).


--------------------------- assert (* Cut *) (euclidean__axioms.Col R B A) as H36.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H36.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B R H1).
----------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H44.
---------------------------- assert (* Cut *) (~(euclidean__axioms.neq R B)) as H37.
----------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.Col B P A) as H38.
------------------------------ apply (@euclidean__tactics.not__nCol__Col B P A).
-------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False B P A H38).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 R B P A H35 H36 H37).


------------------------------ assert (* Cut *) (euclidean__axioms.Col A B P) as H39.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))))) as H39.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B P A H38).
-------------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H44.
------------------------------- apply (@euclidean__tactics.Col__nCol__False A B P H11 H39).
----------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H38.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H18).
------------------------------ assert (* Cut *) (euclidean__axioms.neq R A) as H39.
------------------------------- assert (* Cut *) (R = B) as H39.
-------------------------------- apply (@euclidean__tactics.NNPP (R = B) H37).
-------------------------------- assert (* Cut *) (L = R) as H40.
--------------------------------- apply (@euclidean__tactics.NNPP (L = R) H22).
--------------------------------- intro H41.
assert (* Cut *) (A = B) as Heq.
---------------------------------- apply (@logic.eq__trans Point A R B).
-----------------------------------apply (@logic.eq__sym Point R A H41).

----------------------------------- exact H39.
---------------------------------- assert False.
-----------------------------------apply (@H18 Heq).
----------------------------------- contradiction.
------------------------------- assert (* Cut *) (euclidean__axioms.Col B A R) as H40.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R A B) /\ (euclidean__axioms.Col A B R))))) as H40.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder R B A H36).
--------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H43.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B A Q) as H41.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H41.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B Q H27).
---------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H42.
--------------------------------- assert (euclidean__axioms.neq B A) as H42 by exact H38.
assert (* Cut *) (euclidean__axioms.Col A Q R) as H43.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col A Q R).
-----------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False A Q R H43).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 B A Q R H41 H40 H42).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col R A Q) as H44.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q A R) /\ ((euclidean__axioms.Col Q R A) /\ ((euclidean__axioms.Col R A Q) /\ ((euclidean__axioms.Col A R Q) /\ (euclidean__axioms.Col R Q A))))) as H44.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A Q R H43).
------------------------------------ destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col Q R A) as H45.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A R Q) /\ ((euclidean__axioms.Col A Q R) /\ ((euclidean__axioms.Col Q R A) /\ ((euclidean__axioms.Col R Q A) /\ (euclidean__axioms.Col Q A R))))) as H45.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder R A Q H44).
------------------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H50.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col R A P) as H46.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col R A P).
--------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False R A P H46).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 Q R A P H45 H33 H34).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col R A B) as H47.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H47.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A R H40).
--------------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col A P B) as H48.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col A P B).
----------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False A P B H48).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 R A P B H46 H47 H39).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H49.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))))) as H49.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A P B H48).
----------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H56.
---------------------------------------- apply (@euclidean__tactics.Col__nCol__False A B P H11 H49).
-------------------- assert (* Cut *) (euclidean__axioms.TS Q A B C) as H28.
--------------------- exists R.
split.
---------------------- exact H26.
---------------------- split.
----------------------- exact H1.
----------------------- apply (@euclidean__tactics.nCol__notCol A B Q H27).
--------------------- exact H28.
-- exact H3.
Qed.
