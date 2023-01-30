Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__doublereverse.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__midpointunique.
Require Export lemma__partnotequalwhole.
Require Export logic.
Definition lemma__rightangleNC : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Per A B C) -> (euclidean__axioms.nCol A B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H0.
- exact H.
- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))))) as H1.
-- exact H0.
-- destruct H1 as [D H1].
assert (* AndElim *) ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.Cong A B B D) as H8.
------ assert (* Cut *) ((euclidean__axioms.Cong B A B D) /\ ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D))) as H8.
------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (B) H4).
------- assert (* AndElim *) ((euclidean__axioms.Cong B A B D) /\ ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D)) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
exact H12.
------ assert (* Cut *) (euclidean__defs.Midpoint A B D) as H9.
------- split.
-------- exact H2.
-------- exact H8.
------- assert (* Cut *) (~(euclidean__axioms.BetS A C D)) as H10.
-------- intro H10.
assert (* Cut *) (euclidean__axioms.Cong A C C D) as H11.
--------- assert (* Cut *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H11.
---------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (D) (C) H6).
---------- assert (* AndElim *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
exact H15.
--------- assert (* Cut *) (euclidean__defs.Midpoint A C D) as H12.
---------- split.
----------- exact H10.
----------- exact H11.
---------- assert (* Cut *) (B = C) as H13.
----------- apply (@lemma__midpointunique.lemma__midpointunique (A) (B) (D) (C) (H9) H12).
----------- apply (@H7 H13).
-------- assert (* Cut *) (euclidean__axioms.neq A B) as H11.
--------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H11.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (D) H2).
---------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
exact H14.
--------- assert (* Cut *) (~(C = A)) as H12.
---------- intro H12.
assert (* Cut *) (euclidean__axioms.Cong C C D C) as H13.
----------- apply (@eq__ind__r euclidean__axioms.Point A (fun C0: euclidean__axioms.Point => (euclidean__defs.Per A B C0) -> ((euclidean__axioms.Cong A C0 D C0) -> ((euclidean__axioms.neq B C0) -> ((~(euclidean__axioms.BetS A C0 D)) -> (euclidean__axioms.Cong C0 C0 D C0)))))) with (x := C).
------------intro H13.
intro H14.
intro H15.
intro H16.
exact H14.

------------ exact H12.
------------ exact H.
------------ exact H6.
------------ exact H7.
------------ exact H10.
----------- assert (* Cut *) (euclidean__axioms.Cong D C C C) as H14.
------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (C) (C) (C) H13).
------------ assert (* Cut *) (~(euclidean__axioms.neq D C)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.neq C C) as H16.
-------------- apply (@euclidean__axioms.axiom__nocollapse (D) (C) (C) (C) (H15) H14).
-------------- assert (* Cut *) (C = C) as H17.
--------------- assert (* Cut *) (False) as H17.
---------------- assert (* Cut *) (C = C) as H17.
----------------- apply (@logic.eq__refl (Point) C).
----------------- apply (@H16 H17).
---------------- assert (* Cut *) (False) as H18.
----------------- exact H17.
----------------- apply (@logic.eq__refl (Point) C).
--------------- apply (@H16 H17).
------------- assert (* Cut *) (A = C) as H16.
-------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (C) H12).
-------------- assert (* Cut *) (D = A) as H17.
--------------- assert (* Cut *) (D = C) as H17.
---------------- apply (@euclidean__tactics.NNPP (D = C) H15).
---------------- apply (@logic.eq__trans (Point) (D) (C) (A) (H17)).
-----------------apply (@logic.eq__sym (Point) (A) (C) H16).

--------------- assert (* Cut *) (A = D) as H18.
---------------- apply (@eq__ind__r euclidean__axioms.Point A (fun D0: euclidean__axioms.Point => (euclidean__axioms.BetS A B D0) -> ((euclidean__axioms.Cong A B D0 B) -> ((euclidean__axioms.Cong A C D0 C) -> ((euclidean__axioms.Cong A B B D0) -> ((euclidean__defs.Midpoint A B D0) -> ((~(euclidean__axioms.BetS A C D0)) -> ((euclidean__axioms.Cong C C D0 C) -> ((euclidean__axioms.Cong D0 C C C) -> ((~(euclidean__axioms.neq D0 C)) -> (A = D0))))))))))) with (x := D).
-----------------intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
apply (@eq__ind euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__defs.Per A0 B C) -> ((euclidean__axioms.Cong A0 C A0 C) -> ((euclidean__axioms.Cong A0 B A0 B) -> ((euclidean__axioms.BetS A0 B A0) -> ((~(euclidean__axioms.BetS A0 C A0)) -> ((euclidean__defs.Midpoint A0 B A0) -> ((euclidean__axioms.Cong A0 B B A0) -> ((euclidean__axioms.neq A0 B) -> ((~(euclidean__axioms.neq A0 C)) -> ((euclidean__axioms.Cong A0 C C C) -> ((euclidean__axioms.Cong C C A0 C) -> ((A0 = C) -> (A0 = A0)))))))))))))) with (y := A).
------------------intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
assert (* Cut *) (C = C) as H39.
------------------- exact H38.
------------------- exact H39.

------------------ exact H12.
------------------ exact H.
------------------ exact H20.
------------------ exact H19.
------------------ exact H18.
------------------ exact H23.
------------------ exact H22.
------------------ exact H21.
------------------ exact H11.
------------------ exact H26.
------------------ exact H25.
------------------ exact H24.
------------------ exact H16.

----------------- exact H17.
----------------- exact H2.
----------------- exact H4.
----------------- exact H6.
----------------- exact H8.
----------------- exact H9.
----------------- exact H10.
----------------- exact H13.
----------------- exact H14.
----------------- exact H15.
---------------- assert (* Cut *) (euclidean__axioms.neq A D) as H19.
----------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H19.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (D) H2).
------------------ assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
exact H23.
----------------- apply (@H19 H18).
---------- assert (* Cut *) (~(C = D)) as H13.
----------- intro H13.
assert (* Cut *) (euclidean__axioms.Cong A C D D) as H14.
------------ apply (@eq__ind__r euclidean__axioms.Point D (fun C0: euclidean__axioms.Point => (euclidean__defs.Per A B C0) -> ((euclidean__axioms.Cong A C0 D C0) -> ((euclidean__axioms.neq B C0) -> ((~(euclidean__axioms.BetS A C0 D)) -> ((~(C0 = A)) -> (euclidean__axioms.Cong A C0 D D))))))) with (x := C).
-------------intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
exact H15.

------------- exact H13.
------------- exact H.
------------- exact H6.
------------- exact H7.
------------- exact H10.
------------- exact H12.
------------ assert (* Cut *) (~(euclidean__axioms.neq A C)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.neq D D) as H16.
-------------- apply (@euclidean__axioms.axiom__nocollapse (A) (C) (D) (D) (H15) H14).
-------------- assert (* Cut *) (D = D) as H17.
--------------- assert (* Cut *) (False) as H17.
---------------- assert (* Cut *) (D = D) as H17.
----------------- apply (@logic.eq__refl (Point) D).
----------------- apply (@H16 H17).
---------------- assert (* Cut *) (False) as H18.
----------------- exact H17.
----------------- apply (@logic.eq__refl (Point) D).
--------------- apply (@H16 H17).
------------- assert (* Cut *) (C = A) as H16.
-------------- assert (* Cut *) (False) as H16.
--------------- assert (* Cut *) (~(A = C)) as H16.
---------------- intro H16.
apply (@H12).
-----------------apply (@logic.eq__sym (Point) (A) (C) H16).

---------------- apply (@H15 H16).
--------------- assert (* Cut *) (False) as H17.
---------------- exact H16.
---------------- assert False.
-----------------exact H17.
----------------- contradiction.
-------------- apply (@H12 H16).
----------- assert (* Cut *) (~(euclidean__axioms.BetS C A D)) as H14.
------------ intro H14.
assert (* Cut *) (euclidean__axioms.Cong C A C D) as H15.
------------- assert (* Cut *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H15.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (D) (C) H6).
-------------- assert (* AndElim *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D)) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
exact H16.
------------- assert (* Cut *) (~(euclidean__axioms.Cong C A C D)) as H16.
-------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (C) (A) (D) H14).
-------------- apply (@H16 H15).
------------ assert (* Cut *) (~(euclidean__axioms.BetS A D C)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.BetS C D A) as H16.
-------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (C) H15).
-------------- assert (* Cut *) (euclidean__axioms.Cong C D C A) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.Cong C D C A) /\ (euclidean__axioms.Cong C A C D)) as H17.
---------------- apply (@lemma__doublereverse.lemma__doublereverse (A) (C) (D) (C) H6).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong C D C A) /\ (euclidean__axioms.Cong C A C D)) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
exact H18.
--------------- assert (* Cut *) (~(euclidean__axioms.Cong C D C A)) as H18.
---------------- apply (@lemma__partnotequalwhole.lemma__partnotequalwhole (C) (D) (A) H16).
---------------- apply (@H18 H17).
------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H16.
-------------- intro H16.
assert (* Cut *) (euclidean__axioms.Col A B D) as H17.
--------------- right.
right.
right.
right.
left.
exact H2.
--------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H18.
---------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H18.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (C) H16).
----------------- assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A)) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
exact H19.
---------------- assert (* Cut *) (euclidean__axioms.Col B A D) as H19.
----------------- assert (* Cut *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H19.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (D) H17).
------------------ assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
exact H20.
----------------- assert (* Cut *) (euclidean__axioms.neq B A) as H20.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H11).
------------------ assert (* Cut *) (euclidean__axioms.Col A C D) as H21.
------------------- apply (@euclidean__tactics.not__nCol__Col (A) (C) (D)).
--------------------intro H21.
apply (@euclidean__tactics.Col__nCol__False (A) (C) (D) (H21)).
---------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (C) (D) (H18) (H19) H20).


------------------- assert (* Cut *) ((A = C) \/ ((A = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C)))))) as H22.
-------------------- exact H21.
-------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H23.
--------------------- assert (* Cut *) ((A = C) \/ ((A = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C)))))) as H23.
---------------------- exact H22.
---------------------- assert (* Cut *) ((A = C) \/ ((A = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C)))))) as __TmpHyp.
----------------------- exact H23.
----------------------- assert (A = C \/ (A = D) \/ ((C = D) \/ ((euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C))))) as H24.
------------------------ exact __TmpHyp.
------------------------ destruct H24 as [H24|H24].
------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H25.
-------------------------- intro H25.
assert (* Cut *) (euclidean__axioms.neq A C) as H26.
--------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__defs.Per A0 B C) -> ((euclidean__axioms.BetS A0 B D) -> ((euclidean__axioms.Cong A0 B D B) -> ((euclidean__axioms.Cong A0 C D C) -> ((euclidean__axioms.Cong A0 B B D) -> ((euclidean__defs.Midpoint A0 B D) -> ((~(euclidean__axioms.BetS A0 C D)) -> ((euclidean__axioms.neq A0 B) -> ((~(C = A0)) -> ((~(euclidean__axioms.BetS C A0 D)) -> ((~(euclidean__axioms.BetS A0 D C)) -> ((euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Col A0 B D) -> ((euclidean__axioms.Col B A0 C) -> ((euclidean__axioms.Col B A0 D) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 C D) -> ((euclidean__axioms.Col A0 B C) -> (euclidean__axioms.neq A0 C)))))))))))))))))))) with (x := A).
----------------------------intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
exact H34.

---------------------------- exact H24.
---------------------------- exact H.
---------------------------- exact H2.
---------------------------- exact H4.
---------------------------- exact H6.
---------------------------- exact H8.
---------------------------- exact H9.
---------------------------- exact H10.
---------------------------- exact H11.
---------------------------- exact H12.
---------------------------- exact H14.
---------------------------- exact H15.
---------------------------- exact H16.
---------------------------- exact H17.
---------------------------- exact H18.
---------------------------- exact H19.
---------------------------- exact H20.
---------------------------- exact H21.
---------------------------- exact H25.
--------------------------- apply (@H26 H24).
-------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H25).
------------------------- assert (A = D \/ (C = D) \/ ((euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C)))) as H25.
-------------------------- exact H24.
-------------------------- destruct H25 as [H25|H25].
--------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H26.
---------------------------- intro H26.
assert (* Cut *) (euclidean__axioms.neq A D) as H27.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H27.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (D) H2).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H28.
------------------------------- exact H27.
------------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)) as H30.
-------------------------------- exact H29.
-------------------------------- destruct H30 as [H30 H31].
exact H31.
----------------------------- apply (@H27 H25).
---------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H26).
--------------------------- assert (C = D \/ (euclidean__axioms.BetS C A D) \/ ((euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C))) as H26.
---------------------------- exact H25.
---------------------------- destruct H26 as [H26|H26].
----------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H27.
------------------------------ intro H27.
apply (@H13 H26).
------------------------------ apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H27).
----------------------------- assert (euclidean__axioms.BetS C A D \/ (euclidean__axioms.BetS A C D) \/ (euclidean__axioms.BetS A D C)) as H27.
------------------------------ exact H26.
------------------------------ destruct H27 as [H27|H27].
------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H28.
-------------------------------- intro H28.
apply (@H14 H27).
-------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H28).
------------------------------- assert (euclidean__axioms.BetS A C D \/ euclidean__axioms.BetS A D C) as H28.
-------------------------------- exact H27.
-------------------------------- destruct H28 as [H28|H28].
--------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H29.
---------------------------------- intro H29.
apply (@H10 H28).
---------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H29).
--------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H29.
---------------------------------- intro H29.
apply (@H15 H28).
---------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H29).
--------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H23) H16).
-------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H16).
Qed.
