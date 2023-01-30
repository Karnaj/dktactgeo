Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rightangleNC.
Require Export logic.
Definition lemma__collinearright : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Per A B D) -> ((euclidean__axioms.Col A B C) -> ((euclidean__axioms.neq C B) -> (euclidean__defs.Per C B D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H2.
- exact H0.
- assert (* Cut *) (euclidean__axioms.nCol A B D) as H3.
-- apply (@lemma__rightangleNC.lemma__rightangleNC (A) (B) (D) H).
-- assert (* Cut *) (~(A = B)) as H4.
--- intro H4.
assert (* Cut *) (euclidean__axioms.nCol A A D) as H5.
---- apply (@eq__ind__r euclidean__axioms.Point B (fun A0: euclidean__axioms.Point => (euclidean__defs.Per A0 B D) -> ((euclidean__axioms.Col A0 B C) -> (((A0 = B) \/ ((A0 = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A0 C) \/ ((euclidean__axioms.BetS A0 B C) \/ (euclidean__axioms.BetS A0 C B)))))) -> ((euclidean__axioms.nCol A0 B D) -> (euclidean__axioms.nCol A0 A0 D)))))) with (x := A).
-----intro H5.
intro H6.
intro H7.
intro H8.
exact H8.

----- exact H4.
----- exact H.
----- exact H0.
----- exact H2.
----- exact H3.
---- assert (* Cut *) (A = A) as H6.
----- apply (@logic.eq__refl (Point) A).
----- assert (* Cut *) (euclidean__axioms.Col D A A) as H7.
------ right.
right.
left.
exact H6.
------ assert (* Cut *) (euclidean__axioms.Col A A D) as H8.
------- assert (* Cut *) ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col A A D) /\ ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col D A A) /\ (euclidean__axioms.Col A A D))))) as H8.
-------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (A) H7).
-------- assert (* AndElim *) ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col A A D) /\ ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col D A A) /\ (euclidean__axioms.Col A A D))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A A D) /\ ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col D A A) /\ (euclidean__axioms.Col A A D)))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A D A) /\ ((euclidean__axioms.Col D A A) /\ (euclidean__axioms.Col A A D))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col D A A) /\ (euclidean__axioms.Col A A D)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
exact H16.
------- apply (@euclidean__tactics.Col__nCol__False (A) (A) (D) (H5) H8).
--- assert (* Cut *) (euclidean__defs.Per D B A) as H5.
---- apply (@lemma__8__2.lemma__8__2 (A) (B) (D) H).
---- assert (* Cut *) (euclidean__defs.Per D B C) as H6.
----- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H6.
------ exact H2.
------ assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as __TmpHyp.
------- exact H6.
------- assert (A = B \/ (A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as H7.
-------- exact __TmpHyp.
-------- destruct H7 as [H7|H7].
--------- assert (* Cut *) (~(~(euclidean__defs.Per D B C))) as H8.
---------- intro H8.
assert (* Cut *) (euclidean__axioms.Col A B D) as H9.
----------- left.
exact H7.
----------- apply (@H4 H7).
---------- apply (@euclidean__tactics.NNPP (euclidean__defs.Per D B C)).
-----------intro H9.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H10.
------------ exact H3.
------------ destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H12.
------------- exact H11.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* Cut *) (False) as H20.
----------------- apply (@H4 H7).
----------------- assert (* Cut *) (False) as H21.
------------------ apply (@H8 H9).
------------------ assert False.
-------------------exact H21.
------------------- contradiction.

--------- assert (A = C \/ (B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) as H8.
---------- exact H7.
---------- destruct H8 as [H8|H8].
----------- assert (* Cut *) (euclidean__defs.Per D B C) as H9.
------------ apply (@eq__ind__r euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__defs.Per A0 B D) -> ((euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.nCol A0 B D) -> ((~(A0 = B)) -> ((euclidean__defs.Per D B A0) -> (euclidean__defs.Per D B C))))))) with (x := A).
-------------intro H9.
intro H10.
intro H11.
intro H12.
intro H13.
exact H13.

------------- exact H8.
------------- exact H.
------------- exact H0.
------------- exact H3.
------------- exact H4.
------------- exact H5.
------------ exact H9.
----------- assert (B = C \/ (euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as H9.
------------ exact H8.
------------ destruct H9 as [H9|H9].
------------- assert (* Cut *) (~(~(euclidean__defs.Per D B C))) as H10.
-------------- intro H10.
assert (* Cut *) (C = B) as H11.
--------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (C) (B) H9).
--------------- apply (@H1 H11).
-------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Per D B C)).
---------------intro H11.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H12.
---------------- exact H3.
---------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H14.
----------------- exact H13.
----------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H16.
------------------ exact H15.
------------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H18.
------------------- exact H17.
------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H20.
-------------------- exact H19.
-------------------- destruct H20 as [H20 H21].
assert (* Cut *) (False) as H22.
--------------------- apply (@H10 H11).
--------------------- assert False.
----------------------exact H22.
---------------------- contradiction.

------------- assert (euclidean__axioms.BetS B A C \/ (euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) as H10.
-------------- exact H9.
-------------- destruct H10 as [H10|H10].
--------------- assert (* Cut *) (euclidean__axioms.neq B A) as H11.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H4).
---------------- assert (* Cut *) (euclidean__defs.Out B A C) as H12.
----------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (C)).
------------------right.
right.
exact H10.

------------------ exact H11.
----------------- assert (* Cut *) (euclidean__defs.Per D B C) as H13.
------------------ apply (@lemma__8__3.lemma__8__3 (D) (B) (A) (C) (H5) H12).
------------------ exact H13.
--------------- assert (euclidean__axioms.BetS A B C \/ euclidean__axioms.BetS A C B) as H11.
---------------- exact H10.
---------------- destruct H11 as [H11|H11].
----------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A D E D) /\ (euclidean__axioms.neq B D)))) as H12.
------------------ exact H.
------------------ assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A D E D) /\ (euclidean__axioms.neq B D))))) as H13.
------------------- exact H12.
------------------- destruct H13 as [E H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B E) /\ ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A D E D) /\ (euclidean__axioms.neq B D)))) as H14.
-------------------- exact H13.
-------------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong A B E B) /\ ((euclidean__axioms.Cong A D E D) /\ (euclidean__axioms.neq B D))) as H16.
--------------------- exact H15.
--------------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A D E D) /\ (euclidean__axioms.neq B D)) as H18.
---------------------- exact H17.
---------------------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.BetS E B A) as H20.
----------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (E) H14).
----------------------- assert (* Cut *) (euclidean__axioms.Cong E B A B) as H21.
------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (A) (B) (B) H16).
------------------------ assert (* Cut *) (euclidean__axioms.Cong E D A D) as H22.
------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (A) (D) (D) H18).
------------------------- assert (* Cut *) (euclidean__defs.Per E B D) as H23.
-------------------------- exists A.
split.
--------------------------- exact H20.
--------------------------- split.
---------------------------- exact H21.
---------------------------- split.
----------------------------- exact H22.
----------------------------- exact H19.
-------------------------- assert (* Cut *) (euclidean__defs.Per D B E) as H24.
--------------------------- apply (@lemma__8__2.lemma__8__2 (E) (B) (D) H23).
--------------------------- assert (* Cut *) (euclidean__axioms.BetS A B E) as H25.
---------------------------- exact H14.
---------------------------- assert (* Cut *) (euclidean__defs.Out B E C) as H26.
----------------------------- exists A.
split.
------------------------------ exact H11.
------------------------------ exact H25.
----------------------------- assert (* Cut *) (euclidean__defs.Per D B C) as H27.
------------------------------ apply (@lemma__8__3.lemma__8__3 (D) (B) (E) (C) (H24) H26).
------------------------------ exact H27.
----------------- assert (* Cut *) (euclidean__axioms.BetS B C A) as H12.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (C) (B) H11).
------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H13.
------------------- assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))) as H13.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (C) (A) H12).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))) as H14.
--------------------- exact H13.
--------------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)) as H16.
---------------------- exact H15.
---------------------- destruct H16 as [H16 H17].
exact H1.
------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H14.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (B) H13).
-------------------- assert (* Cut *) (euclidean__defs.Out B C A) as H15.
--------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (A)).
----------------------right.
right.
exact H12.

---------------------- exact H14.
--------------------- assert (* Cut *) (euclidean__defs.Per D B A) as H16.
---------------------- exact H5.
---------------------- assert (* Cut *) (euclidean__defs.Out B A C) as H17.
----------------------- apply (@lemma__ray5.lemma__ray5 (B) (C) (A) H15).
----------------------- assert (* Cut *) (euclidean__defs.Per D B C) as H18.
------------------------ apply (@lemma__8__3.lemma__8__3 (D) (B) (A) (C) (H16) H17).
------------------------ exact H18.
----- assert (* Cut *) (euclidean__defs.Per C B D) as H7.
------ apply (@lemma__8__2.lemma__8__2 (D) (B) (C) H6).
------ exact H7.
Qed.
