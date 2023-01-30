Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__ABCequalsCBA.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__differenceofparts.
Require Export lemma__doublereverse.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglestransitive.
Require Export lemma__extensionunique.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__outerconnectivity.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Require Export proposition__04.
Require Export proposition__15.
Definition lemma__pointreflectionisometry : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__defs.Midpoint A B C) -> ((euclidean__defs.Midpoint P B Q) -> ((euclidean__axioms.neq A P) -> (euclidean__axioms.Cong A P C Q))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H2.
- assert (* Cut *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H2.
-- exact H0.
-- assert (* Cut *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as __TmpHyp.
--- exact H2.
--- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H3.
---- exact __TmpHyp.
---- destruct H3 as [H3 H4].
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H5.
----- exact H.
----- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp0.
------ exact H5.
------ assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H6.
------- exact __TmpHyp0.
------- destruct H6 as [H6 H7].
split.
-------- exact H6.
-------- exact H7.
- assert (* Cut *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H3.
-- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H3.
--- exact H2.
--- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp.
---- exact H3.
---- assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H4.
----- exact __TmpHyp.
----- destruct H4 as [H4 H5].
assert (* Cut *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H6.
------ exact H0.
------ assert (* Cut *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as __TmpHyp0.
------- exact H6.
------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H7.
-------- exact __TmpHyp0.
-------- destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
--------- exact H.
--------- assert (* Cut *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as __TmpHyp1.
---------- exact H9.
---------- assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H10.
----------- exact __TmpHyp1.
----------- destruct H10 as [H10 H11].
split.
------------ exact H7.
------------ exact H8.
-- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H4.
--- assert (* Cut *) ((euclidean__axioms.Col A B P) \/ (euclidean__axioms.nCol A B P)) as H4.
---- apply (@euclidean__tactics.Col__or__nCol (A) (B) P).
---- assert (* Cut *) ((euclidean__axioms.Col A B P) \/ (euclidean__axioms.nCol A B P)) as H5.
----- exact H4.
----- assert (* Cut *) ((euclidean__axioms.Col A B P) \/ (euclidean__axioms.nCol A B P)) as __TmpHyp.
------ exact H5.
------ assert (euclidean__axioms.Col A B P \/ euclidean__axioms.nCol A B P) as H6.
------- exact __TmpHyp.
------- destruct H6 as [H6|H6].
-------- assert (* Cut *) ((A = B) \/ ((A = P) \/ ((B = P) \/ ((euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B)))))) as H7.
--------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H7.
---------- exact H3.
---------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
----------- exact H2.
----------- destruct H9 as [H9 H10].
exact H6.
--------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H8.
---------- assert (* Cut *) ((A = B) \/ ((A = P) \/ ((B = P) \/ ((euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B)))))) as H8.
----------- exact H7.
----------- assert (* Cut *) ((A = B) \/ ((A = P) \/ ((B = P) \/ ((euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B)))))) as __TmpHyp0.
------------ exact H8.
------------ assert (A = B \/ (A = P) \/ ((B = P) \/ ((euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B))))) as H9.
------------- exact __TmpHyp0.
------------- destruct H9 as [H9|H9].
-------------- assert (* Cut *) (~(~(euclidean__axioms.Cong A P C Q))) as H10.
--------------- intro H10.
assert (* Cut *) (euclidean__axioms.BetS A B C) as H11.
---------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H11.
----------------- exact H3.
----------------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H13.
------------------ exact H2.
------------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H15.
------------------- exact H0.
------------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H17.
-------------------- exact H.
-------------------- destruct H17 as [H17 H18].
exact H13.
---------------- assert (* Cut *) (euclidean__axioms.neq A B) as H12.
----------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H12.
------------------ exact H3.
------------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H14.
------------------- exact H2.
------------------- destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H16.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (C) H11).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H17.
--------------------- exact H16.
--------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H19.
---------------------- exact H18.
---------------------- destruct H19 as [H19 H20].
exact H19.
----------------- apply (@H12 H9).
--------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.Cong A P C Q)).
----------------intro H11.
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H12.
----------------- exact H2.
----------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H14.
------------------ exact H3.
------------------ destruct H14 as [H14 H15].
assert (* Cut *) (False) as H16.
------------------- apply (@H10 H11).
------------------- assert False.
--------------------exact H16.
-------------------- contradiction.

-------------- assert (A = P \/ (B = P) \/ ((euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B)))) as H10.
--------------- exact H9.
--------------- destruct H10 as [H10|H10].
---------------- assert (* Cut *) (~(~(euclidean__axioms.Cong A P C Q))) as H11.
----------------- intro H11.
apply (@H1 H10).
----------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.Cong A P C Q)).
------------------intro H12.
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H13.
------------------- exact H2.
------------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H15.
-------------------- exact H3.
-------------------- destruct H15 as [H15 H16].
assert (* Cut *) (False) as H17.
--------------------- apply (@H1 H10).
--------------------- assert (* Cut *) (False) as H18.
---------------------- apply (@H11 H12).
---------------------- assert False.
-----------------------exact H18.
----------------------- contradiction.

---------------- assert (B = P \/ (euclidean__axioms.BetS B A P) \/ ((euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B))) as H11.
----------------- exact H10.
----------------- destruct H11 as [H11|H11].
------------------ assert (* Cut *) (~(~(euclidean__axioms.Cong A P C Q))) as H12.
------------------- intro H12.
assert (* Cut *) (euclidean__axioms.neq P B) as H13.
-------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H13.
--------------------- exact H3.
--------------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H15.
---------------------- exact H2.
---------------------- destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H17.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (B) (Q) H13).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H18.
------------------------ exact H17.
------------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q)) as H20.
------------------------- exact H19.
------------------------- destruct H20 as [H20 H21].
exact H20.
-------------------- assert (* Cut *) (euclidean__axioms.neq B P) as H14.
--------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H14.
---------------------- exact H3.
---------------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H16.
----------------------- exact H2.
----------------------- destruct H16 as [H16 H17].
apply (@eq__ind__r euclidean__axioms.Point P (fun B0: euclidean__axioms.Point => (euclidean__defs.Midpoint A B0 C) -> ((euclidean__defs.Midpoint P B0 Q) -> ((euclidean__axioms.BetS A B0 C) -> ((euclidean__axioms.Cong A B0 B0 C) -> ((euclidean__axioms.BetS P B0 Q) -> ((euclidean__axioms.Cong P B0 B0 Q) -> ((euclidean__axioms.Col A B0 P) -> ((euclidean__axioms.neq P B0) -> (euclidean__axioms.neq B0 P)))))))))) with (x := B).
------------------------intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
exact H25.

------------------------ exact H11.
------------------------ exact H.
------------------------ exact H0.
------------------------ exact H16.
------------------------ exact H17.
------------------------ exact H14.
------------------------ exact H15.
------------------------ exact H6.
------------------------ exact H13.
--------------------- apply (@H14 H11).
------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.Cong A P C Q)).
--------------------intro H13.
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H14.
--------------------- exact H2.
--------------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H16.
---------------------- exact H3.
---------------------- destruct H16 as [H16 H17].
assert (* Cut *) (False) as H18.
----------------------- apply (@H12 H13).
----------------------- assert False.
------------------------exact H18.
------------------------ contradiction.

------------------ assert (euclidean__axioms.BetS B A P \/ (euclidean__axioms.BetS A B P) \/ (euclidean__axioms.BetS A P B)) as H12.
------------------- exact H11.
------------------- destruct H12 as [H12|H12].
-------------------- assert (* Cut *) (euclidean__axioms.Cong B C A B) as H13.
--------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H13.
---------------------- exact H3.
---------------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H15.
----------------------- exact H2.
----------------------- destruct H15 as [H15 H16].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (B) (C) H16).
--------------------- assert (* Cut *) (euclidean__axioms.Cong B C B A) as H14.
---------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H14.
----------------------- exact H3.
----------------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H16.
------------------------ exact H2.
------------------------ destruct H16 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.Cong C B B A) /\ ((euclidean__axioms.Cong C B A B) /\ (euclidean__axioms.Cong B C B A))) as H18.
------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (A) (B) H13).
------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B B A) /\ ((euclidean__axioms.Cong C B A B) /\ (euclidean__axioms.Cong B C B A))) as H19.
-------------------------- exact H18.
-------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong C B A B) /\ (euclidean__axioms.Cong B C B A)) as H21.
--------------------------- exact H20.
--------------------------- destruct H21 as [H21 H22].
exact H22.
---------------------- assert (* Cut *) (euclidean__axioms.Cong Q B B P) as H15.
----------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H15.
------------------------ exact H3.
------------------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H17.
------------------------- exact H2.
------------------------- destruct H17 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.Cong Q B B P) /\ (euclidean__axioms.Cong B P Q B)) as H19.
-------------------------- apply (@lemma__doublereverse.lemma__doublereverse (P) (B) (B) (Q) H16).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q B B P) /\ (euclidean__axioms.Cong B P Q B)) as H20.
--------------------------- exact H19.
--------------------------- destruct H20 as [H20 H21].
exact H20.
----------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B P) as H16.
------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H16.
------------------------- exact H3.
------------------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H18.
-------------------------- exact H2.
-------------------------- destruct H18 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.Cong B Q P B) /\ ((euclidean__axioms.Cong B Q B P) /\ (euclidean__axioms.Cong Q B P B))) as H20.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (Q) (B) (B) (P) H15).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B Q P B) /\ ((euclidean__axioms.Cong B Q B P) /\ (euclidean__axioms.Cong Q B P B))) as H21.
---------------------------- exact H20.
---------------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Cong B Q B P) /\ (euclidean__axioms.Cong Q B P B)) as H23.
----------------------------- exact H22.
----------------------------- destruct H23 as [H23 H24].
exact H23.
------------------------ assert (* Cut *) (euclidean__axioms.Cong B A C B) as H17.
------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H17.
-------------------------- exact H3.
-------------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
--------------------------- exact H2.
--------------------------- destruct H19 as [H19 H20].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ (euclidean__axioms.Cong C B B A)) as H21.
---------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (C) (A) (B) H13).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C B) /\ (euclidean__axioms.Cong C B B A)) as H22.
----------------------------- exact H21.
----------------------------- destruct H22 as [H22 H23].
exact H22.
------------------------- assert (* Cut *) (euclidean__defs.Lt C B B P) as H18.
-------------------------- exists A.
split.
--------------------------- exact H12.
--------------------------- exact H17.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H19.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H19.
---------------------------- exact H3.
---------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
----------------------------- exact H2.
----------------------------- destruct H21 as [H21 H22].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (Q) (P) H16).
--------------------------- assert (* Cut *) (euclidean__defs.Lt C B B Q) as H20.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H20.
----------------------------- exact H3.
----------------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H22.
------------------------------ exact H2.
------------------------------ destruct H22 as [H22 H23].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (B) (B) (P) (B) (Q) (H18) H19).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong C B B C) as H21.
----------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H21.
------------------------------ exact H3.
------------------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H23.
------------------------------- exact H2.
------------------------------- destruct H23 as [H23 H24].
apply (@euclidean__axioms.cn__equalityreverse (C) B).
----------------------------- assert (* Cut *) (euclidean__defs.Lt B C B Q) as H22.
------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H22.
------------------------------- exact H3.
------------------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
-------------------------------- exact H2.
-------------------------------- destruct H24 as [H24 H25].
apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (B) (B) (Q) (B) (C) (H20) H21).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong B Q B Q) as H23.
------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H23.
-------------------------------- exact H3.
-------------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H25.
--------------------------------- exact H2.
--------------------------------- destruct H25 as [H25 H26].
apply (@euclidean__axioms.cn__congruencereflexive (B) Q).
------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H24.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H24.
--------------------------------- exact H3.
--------------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H26.
---------------------------------- exact H2.
---------------------------------- destruct H26 as [H26 H27].
assert (* Cut *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H28.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (B) (Q) H24).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H29.
------------------------------------ exact H28.
------------------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q)) as H31.
------------------------------------- exact H30.
------------------------------------- destruct H31 as [H31 H32].
exact H29.
-------------------------------- assert (* Cut *) (exists (H25: euclidean__axioms.Point), (euclidean__axioms.BetS B H25 Q) /\ (euclidean__axioms.Cong B H25 B C)) as H25.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H25.
---------------------------------- exact H3.
---------------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H27.
----------------------------------- exact H2.
----------------------------------- destruct H27 as [H27 H28].
exact H22.
--------------------------------- assert (exists H26: euclidean__axioms.Point, ((euclidean__axioms.BetS B H26 Q) /\ (euclidean__axioms.Cong B H26 B C))) as H27.
---------------------------------- exact H25.
---------------------------------- destruct H27 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS B H26 Q) /\ (euclidean__axioms.Cong B H26 B C)) as H28.
----------------------------------- exact H27.
----------------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H30.
------------------------------------ exact H3.
------------------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H32.
------------------------------------- exact H2.
------------------------------------- destruct H32 as [H32 H33].
assert (* Cut *) (euclidean__defs.Out B Q H26) as H34.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (Q) (H26)).
---------------------------------------left.
exact H28.

--------------------------------------- exact H24.
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P A B) as H35.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (P) H12).
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P B C) as H36.
---------------------------------------- apply (@lemma__3__7a.lemma__3__7a (P) (A) (B) (C) (H35) H32).
---------------------------------------- assert (* Cut *) (euclidean__defs.Out B C Q) as H37.
----------------------------------------- exists P.
split.
------------------------------------------ exact H30.
------------------------------------------ exact H36.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q C) as H38.
------------------------------------------ apply (@lemma__ray5.lemma__ray5 (B) (C) (Q) H37).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B C B H26) as H39.
------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (H26) (C) H29).
------------------------------------------- assert (* Cut *) (C = H26) as H40.
-------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (B) (Q) (C) (H26) (H38) (H34) H39).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B C Q) as H41.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H26 (fun C0: euclidean__axioms.Point => (euclidean__defs.Midpoint A B C0) -> ((euclidean__axioms.BetS A B C0) -> ((euclidean__axioms.Cong A B B C0) -> ((euclidean__axioms.Cong B C0 A B) -> ((euclidean__axioms.Cong B C0 B A) -> ((euclidean__axioms.Cong B A C0 B) -> ((euclidean__defs.Lt C0 B B P) -> ((euclidean__defs.Lt C0 B B Q) -> ((euclidean__axioms.Cong C0 B B C0) -> ((euclidean__defs.Lt B C0 B Q) -> ((euclidean__axioms.Cong B H26 B C0) -> ((euclidean__axioms.BetS P B C0) -> ((euclidean__defs.Out B C0 Q) -> ((euclidean__defs.Out B Q C0) -> ((euclidean__axioms.Cong B C0 B H26) -> (euclidean__axioms.BetS B C0 Q))))))))))))))))) with (x := C).
----------------------------------------------intro H41.
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
intro H53.
intro H54.
intro H55.
exact H28.

---------------------------------------------- exact H40.
---------------------------------------------- exact H.
---------------------------------------------- exact H32.
---------------------------------------------- exact H33.
---------------------------------------------- exact H13.
---------------------------------------------- exact H14.
---------------------------------------------- exact H17.
---------------------------------------------- exact H18.
---------------------------------------------- exact H20.
---------------------------------------------- exact H21.
---------------------------------------------- exact H22.
---------------------------------------------- exact H29.
---------------------------------------------- exact H36.
---------------------------------------------- exact H37.
---------------------------------------------- exact H38.
---------------------------------------------- exact H39.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B A P) as H42.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H26 (fun C0: euclidean__axioms.Point => (euclidean__defs.Midpoint A B C0) -> ((euclidean__axioms.BetS A B C0) -> ((euclidean__axioms.Cong A B B C0) -> ((euclidean__axioms.Cong B C0 A B) -> ((euclidean__axioms.Cong B C0 B A) -> ((euclidean__axioms.Cong B A C0 B) -> ((euclidean__defs.Lt C0 B B P) -> ((euclidean__defs.Lt C0 B B Q) -> ((euclidean__axioms.Cong C0 B B C0) -> ((euclidean__defs.Lt B C0 B Q) -> ((euclidean__axioms.Cong B H26 B C0) -> ((euclidean__axioms.BetS P B C0) -> ((euclidean__defs.Out B C0 Q) -> ((euclidean__defs.Out B Q C0) -> ((euclidean__axioms.Cong B C0 B H26) -> ((euclidean__axioms.BetS B C0 Q) -> (euclidean__axioms.BetS B A P)))))))))))))))))) with (x := C).
-----------------------------------------------intro H42.
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
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
exact H12.

----------------------------------------------- exact H40.
----------------------------------------------- exact H.
----------------------------------------------- exact H32.
----------------------------------------------- exact H33.
----------------------------------------------- exact H13.
----------------------------------------------- exact H14.
----------------------------------------------- exact H17.
----------------------------------------------- exact H18.
----------------------------------------------- exact H20.
----------------------------------------------- exact H21.
----------------------------------------------- exact H22.
----------------------------------------------- exact H29.
----------------------------------------------- exact H36.
----------------------------------------------- exact H37.
----------------------------------------------- exact H38.
----------------------------------------------- exact H39.
----------------------------------------------- exact H41.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B C) as H43.
----------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (C) (A) H14).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H44.
------------------------------------------------ apply (@lemma__differenceofparts.lemma__differenceofparts (B) (A) (P) (B) (C) (Q) (H43) (H19) (H42) H41).
------------------------------------------------ exact H44.
-------------------- assert (euclidean__axioms.BetS A B P \/ euclidean__axioms.BetS A P B) as H13.
--------------------- exact H12.
--------------------- destruct H13 as [H13|H13].
---------------------- assert (* Cut *) (~(~(euclidean__axioms.Cong A P C Q))) as H14.
----------------------- intro H14.
assert (* Cut *) (~(euclidean__axioms.BetS B P C)) as H15.
------------------------ intro H15.
assert (* Cut *) (euclidean__axioms.BetS C P B) as H16.
------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H16.
-------------------------- exact H3.
-------------------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H18.
--------------------------- exact H2.
--------------------------- destruct H18 as [H18 H19].
apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (P) (C) H15).
------------------------- assert (* Cut *) (euclidean__axioms.BetS C B Q) as H17.
-------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H17.
--------------------------- exact H3.
--------------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
---------------------------- exact H2.
---------------------------- destruct H19 as [H19 H20].
apply (@lemma__3__7a.lemma__3__7a (C) (P) (B) (Q) (H16) H17).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C B) as H18.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H18.
---------------------------- exact H3.
---------------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
----------------------------- exact H2.
----------------------------- destruct H20 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H22.
------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (B) (C) H21).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H23.
------------------------------- exact H22.
------------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B)) as H25.
-------------------------------- exact H24.
-------------------------------- destruct H25 as [H25 H26].
exact H26.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H19.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H19.
----------------------------- exact H3.
----------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
------------------------------ exact H2.
------------------------------ destruct H21 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H23.
------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (P) (B) (B) (Q) H20).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H24.
-------------------------------- exact H23.
-------------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B)) as H26.
--------------------------------- exact H25.
--------------------------------- destruct H26 as [H26 H27].
exact H26.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H20.
----------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H20.
------------------------------ exact H3.
------------------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H22.
------------------------------- exact H2.
------------------------------- destruct H22 as [H22 H23].
apply (@euclidean__axioms.cn__sumofparts (A) (B) (P) (C) (B) (Q) (H18) (H19) (H13) H17).
----------------------------- apply (@H14 H20).
------------------------ assert (* Cut *) (~(euclidean__axioms.BetS B C P)) as H16.
------------------------- intro H16.
assert (* Cut *) (euclidean__axioms.BetS A B P) as H17.
-------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H17.
--------------------------- exact H3.
--------------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
---------------------------- exact H2.
---------------------------- destruct H19 as [H19 H20].
exact H13.
-------------------------- assert (* Cut *) (euclidean__axioms.BetS Q B P) as H18.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H18.
---------------------------- exact H3.
---------------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
----------------------------- exact H2.
----------------------------- destruct H20 as [H20 H21].
apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (B) (Q) H18).
--------------------------- assert (* Cut *) (euclidean__axioms.BetS Q B C) as H19.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H19.
----------------------------- exact H3.
----------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
------------------------------ exact H2.
------------------------------ destruct H21 as [H21 H22].
apply (@euclidean__axioms.axiom__innertransitivity (Q) (B) (C) (P) (H18) H16).
---------------------------- assert (* Cut *) (euclidean__axioms.BetS C B Q) as H20.
----------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H20.
------------------------------ exact H3.
------------------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H22.
------------------------------- exact H2.
------------------------------- destruct H22 as [H22 H23].
apply (@euclidean__axioms.axiom__betweennesssymmetry (Q) (B) (C) H19).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C B) as H21.
------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H21.
------------------------------- exact H3.
------------------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H23.
-------------------------------- exact H2.
-------------------------------- destruct H23 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H25.
--------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (B) (C) H24).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H26.
---------------------------------- exact H25.
---------------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B)) as H28.
----------------------------------- exact H27.
----------------------------------- destruct H28 as [H28 H29].
exact H29.
------------------------------ assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H22.
------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H22.
-------------------------------- exact H3.
-------------------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
--------------------------------- exact H2.
--------------------------------- destruct H24 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H26.
---------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (P) (B) (B) (Q) H23).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H27.
----------------------------------- exact H26.
----------------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B)) as H29.
------------------------------------ exact H28.
------------------------------------ destruct H29 as [H29 H30].
exact H29.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H23.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H23.
--------------------------------- exact H3.
--------------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H25.
---------------------------------- exact H2.
---------------------------------- destruct H25 as [H25 H26].
apply (@euclidean__axioms.cn__sumofparts (A) (B) (P) (C) (B) (Q) (H21) (H22) (H17) H20).
-------------------------------- apply (@H14 H23).
------------------------- assert (* Cut *) (P = C) as H17.
-------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H17.
--------------------------- exact H3.
--------------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
---------------------------- exact H2.
---------------------------- destruct H19 as [H19 H20].
apply (@lemma__outerconnectivity.lemma__outerconnectivity (A) (B) (P) (C) (H13) (H19) (H15) H16).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B P) as H18.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H18.
---------------------------- exact H3.
---------------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
----------------------------- exact H2.
----------------------------- destruct H20 as [H20 H21].
apply (@eq__ind__r euclidean__axioms.Point C (fun P0: euclidean__axioms.Point => (euclidean__defs.Midpoint P0 B Q) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.BetS P0 B Q) -> ((euclidean__axioms.Cong P0 B B Q) -> ((euclidean__axioms.Col A B P0) -> ((euclidean__axioms.BetS A B P0) -> ((~(euclidean__axioms.Cong A P0 C Q)) -> ((~(euclidean__axioms.BetS B P0 C)) -> ((~(euclidean__axioms.BetS B C P0)) -> (euclidean__axioms.Cong A B B P0))))))))))) with (x := P).
------------------------------intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
exact H21.

------------------------------ exact H17.
------------------------------ exact H0.
------------------------------ exact H1.
------------------------------ exact H18.
------------------------------ exact H19.
------------------------------ exact H6.
------------------------------ exact H13.
------------------------------ exact H14.
------------------------------ exact H15.
------------------------------ exact H16.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H19.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H19.
----------------------------- exact H3.
----------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
------------------------------ exact H2.
------------------------------ destruct H21 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H23.
------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (P) (B) (B) (Q) H20).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H24.
-------------------------------- exact H23.
-------------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B)) as H26.
--------------------------------- exact H25.
--------------------------------- destruct H26 as [H26 H27].
exact H26.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B Q) as H20.
----------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H20.
------------------------------ exact H3.
------------------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H22.
------------------------------- exact H2.
------------------------------- destruct H22 as [H22 H23].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (B) (B) (P) (B) (Q) (H18) H19).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS C B A) as H21.
------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H21.
------------------------------- exact H3.
------------------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H23.
-------------------------------- exact H2.
-------------------------------- destruct H23 as [H23 H24].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (C) H23).
------------------------------ assert (* Cut *) (euclidean__axioms.BetS P B A) as H22.
------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H22.
-------------------------------- exact H3.
-------------------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
--------------------------------- exact H2.
--------------------------------- destruct H24 as [H24 H25].
apply (@eq__ind__r euclidean__axioms.Point C (fun P0: euclidean__axioms.Point => (euclidean__defs.Midpoint P0 B Q) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.BetS P0 B Q) -> ((euclidean__axioms.Cong P0 B B Q) -> ((euclidean__axioms.Col A B P0) -> ((euclidean__axioms.BetS A B P0) -> ((~(euclidean__axioms.Cong A P0 C Q)) -> ((~(euclidean__axioms.BetS B P0 C)) -> ((~(euclidean__axioms.BetS B C P0)) -> ((euclidean__axioms.Cong A B B P0) -> ((euclidean__axioms.Cong B P0 B Q) -> (euclidean__axioms.BetS P0 B A))))))))))))) with (x := P).
----------------------------------intro H26.
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
exact H21.

---------------------------------- exact H17.
---------------------------------- exact H0.
---------------------------------- exact H1.
---------------------------------- exact H22.
---------------------------------- exact H23.
---------------------------------- exact H6.
---------------------------------- exact H13.
---------------------------------- exact H14.
---------------------------------- exact H15.
---------------------------------- exact H16.
---------------------------------- exact H18.
---------------------------------- exact H19.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q A B) as H23.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H23.
--------------------------------- exact H3.
--------------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H25.
---------------------------------- exact H2.
---------------------------------- destruct H25 as [H25 H26].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (B) (Q) H20).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B A) as H24.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H24.
---------------------------------- exact H3.
---------------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H26.
----------------------------------- exact H2.
----------------------------------- destruct H26 as [H26 H27].
assert (* Cut *) ((euclidean__axioms.Cong Q B B A) /\ ((euclidean__axioms.Cong Q B A B) /\ (euclidean__axioms.Cong B Q B A))) as H28.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (B) (Q) (A) (B) H23).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong Q B B A) /\ ((euclidean__axioms.Cong Q B A B) /\ (euclidean__axioms.Cong B Q B A))) as H29.
------------------------------------- exact H28.
------------------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Cong Q B A B) /\ (euclidean__axioms.Cong B Q B A)) as H31.
-------------------------------------- exact H30.
-------------------------------------- destruct H31 as [H31 H32].
exact H32.
--------------------------------- assert (* Cut *) (Q = A) as H25.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H25.
----------------------------------- exact H3.
----------------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H27.
------------------------------------ exact H2.
------------------------------------ destruct H27 as [H27 H28].
apply (@lemma__extensionunique.lemma__extensionunique (P) (B) (Q) (A) (H25) (H22) H24).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C C A) as H26.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H26.
------------------------------------ exact H3.
------------------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H28.
------------------------------------- exact H2.
------------------------------------- destruct H28 as [H28 H29].
apply (@euclidean__axioms.cn__equalityreverse (A) C).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A P C A) as H27.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H27.
------------------------------------- exact H3.
------------------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H29.
-------------------------------------- exact H2.
-------------------------------------- destruct H29 as [H29 H30].
apply (@eq__ind__r euclidean__axioms.Point A (fun Q0: euclidean__axioms.Point => (euclidean__defs.Midpoint P B Q0) -> ((euclidean__axioms.BetS P B Q0) -> ((euclidean__axioms.Cong P B B Q0) -> ((~(euclidean__axioms.Cong A P C Q0)) -> ((euclidean__axioms.Cong B P B Q0) -> ((euclidean__axioms.Cong A B B Q0) -> ((euclidean__axioms.Cong B Q0 A B) -> ((euclidean__axioms.Cong B Q0 B A) -> (euclidean__axioms.Cong A P C A)))))))))) with (x := Q).
---------------------------------------intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
apply (@eq__ind__r euclidean__axioms.Point C (fun P0: euclidean__axioms.Point => (euclidean__defs.Midpoint P0 B A) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.Cong P0 B B A) -> ((euclidean__axioms.BetS P0 B A) -> ((euclidean__axioms.Col A B P0) -> ((euclidean__axioms.BetS A B P0) -> ((~(euclidean__axioms.Cong A P0 C A)) -> ((~(euclidean__axioms.BetS B P0 C)) -> ((~(euclidean__axioms.BetS B C P0)) -> ((euclidean__axioms.Cong A B B P0) -> ((euclidean__axioms.Cong B P0 B A) -> ((euclidean__axioms.BetS P0 B A) -> (euclidean__axioms.Cong A P0 C A)))))))))))))) with (x := P).
----------------------------------------intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
exact H26.

---------------------------------------- exact H17.
---------------------------------------- exact H31.
---------------------------------------- exact H1.
---------------------------------------- exact H33.
---------------------------------------- exact H32.
---------------------------------------- exact H6.
---------------------------------------- exact H13.
---------------------------------------- exact H34.
---------------------------------------- exact H15.
---------------------------------------- exact H16.
---------------------------------------- exact H18.
---------------------------------------- exact H35.
---------------------------------------- exact H22.

--------------------------------------- exact H25.
--------------------------------------- exact H0.
--------------------------------------- exact H27.
--------------------------------------- exact H28.
--------------------------------------- exact H14.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H23.
--------------------------------------- exact H24.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H28.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H28.
-------------------------------------- exact H3.
-------------------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H30.
--------------------------------------- exact H2.
--------------------------------------- destruct H30 as [H30 H31].
apply (@eq__ind__r euclidean__axioms.Point A (fun Q0: euclidean__axioms.Point => (euclidean__defs.Midpoint P B Q0) -> ((euclidean__axioms.BetS P B Q0) -> ((euclidean__axioms.Cong P B B Q0) -> ((~(euclidean__axioms.Cong A P C Q0)) -> ((euclidean__axioms.Cong B P B Q0) -> ((euclidean__axioms.Cong A B B Q0) -> ((euclidean__axioms.Cong B Q0 A B) -> ((euclidean__axioms.Cong B Q0 B A) -> (euclidean__axioms.Cong A P C Q0)))))))))) with (x := Q).
----------------------------------------intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
apply (@eq__ind__r euclidean__axioms.Point C (fun P0: euclidean__axioms.Point => (euclidean__defs.Midpoint P0 B A) -> ((euclidean__axioms.neq A P0) -> ((euclidean__axioms.Cong P0 B B A) -> ((euclidean__axioms.BetS P0 B A) -> ((euclidean__axioms.Col A B P0) -> ((euclidean__axioms.BetS A B P0) -> ((~(euclidean__axioms.Cong A P0 C A)) -> ((~(euclidean__axioms.BetS B P0 C)) -> ((~(euclidean__axioms.BetS B C P0)) -> ((euclidean__axioms.Cong A B B P0) -> ((euclidean__axioms.Cong B P0 B A) -> ((euclidean__axioms.BetS P0 B A) -> ((euclidean__axioms.Cong A P0 C A) -> (euclidean__axioms.Cong A P0 C A))))))))))))))) with (x := P).
-----------------------------------------intro H40.
intro H41.
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
exact H52.

----------------------------------------- exact H17.
----------------------------------------- exact H32.
----------------------------------------- exact H1.
----------------------------------------- exact H34.
----------------------------------------- exact H33.
----------------------------------------- exact H6.
----------------------------------------- exact H13.
----------------------------------------- exact H35.
----------------------------------------- exact H15.
----------------------------------------- exact H16.
----------------------------------------- exact H18.
----------------------------------------- exact H36.
----------------------------------------- exact H22.
----------------------------------------- exact H27.

---------------------------------------- exact H25.
---------------------------------------- exact H0.
---------------------------------------- exact H28.
---------------------------------------- exact H29.
---------------------------------------- exact H14.
---------------------------------------- exact H19.
---------------------------------------- exact H20.
---------------------------------------- exact H23.
---------------------------------------- exact H24.
------------------------------------- apply (@H14 H28).
----------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.Cong A P C Q)).
------------------------intro H15.
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H16.
------------------------- exact H2.
------------------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H18.
-------------------------- exact H3.
-------------------------- destruct H18 as [H18 H19].
assert (* Cut *) (False) as H20.
--------------------------- apply (@H14 H15).
--------------------------- assert False.
----------------------------exact H20.
---------------------------- contradiction.

---------------------- assert (* Cut *) (euclidean__axioms.Cong B Q P B) as H14.
----------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H14.
------------------------ exact H3.
------------------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H16.
------------------------- exact H2.
------------------------- destruct H16 as [H16 H17].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (P) (B) (Q) H15).
----------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B P) as H15.
------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H15.
------------------------- exact H3.
------------------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H17.
-------------------------- exact H2.
-------------------------- destruct H17 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.Cong Q B B P) /\ ((euclidean__axioms.Cong Q B P B) /\ (euclidean__axioms.Cong B Q B P))) as H19.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (Q) (P) (B) H14).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q B B P) /\ ((euclidean__axioms.Cong Q B P B) /\ (euclidean__axioms.Cong B Q B P))) as H20.
---------------------------- exact H19.
---------------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong Q B P B) /\ (euclidean__axioms.Cong B Q B P)) as H22.
----------------------------- exact H21.
----------------------------- destruct H22 as [H22 H23].
exact H23.
------------------------ assert (* Cut *) (euclidean__axioms.Cong C B B A) as H16.
------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H16.
-------------------------- exact H3.
-------------------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H18.
--------------------------- exact H2.
--------------------------- destruct H18 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.Cong C B B A) /\ (euclidean__axioms.Cong B A C B)) as H20.
---------------------------- apply (@lemma__doublereverse.lemma__doublereverse (A) (B) (B) (C) H19).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B B A) /\ (euclidean__axioms.Cong B A C B)) as H21.
----------------------------- exact H20.
----------------------------- destruct H21 as [H21 H22].
exact H21.
------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B A) as H17.
-------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H17.
--------------------------- exact H3.
--------------------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H19.
---------------------------- exact H2.
---------------------------- destruct H19 as [H19 H20].
assert (* Cut *) ((euclidean__axioms.Cong B C A B) /\ ((euclidean__axioms.Cong B C B A) /\ (euclidean__axioms.Cong C B A B))) as H21.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (B) (B) (A) H16).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C A B) /\ ((euclidean__axioms.Cong B C B A) /\ (euclidean__axioms.Cong C B A B))) as H22.
------------------------------ exact H21.
------------------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Cong B C B A) /\ (euclidean__axioms.Cong C B A B)) as H24.
------------------------------- exact H23.
------------------------------- destruct H24 as [H24 H25].
exact H24.
-------------------------- assert (* Cut *) (euclidean__axioms.BetS B P A) as H18.
--------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H18.
---------------------------- exact H3.
---------------------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H20.
----------------------------- exact H2.
----------------------------- destruct H20 as [H20 H21].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (P) (B) H13).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B P Q B) as H19.
---------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H19.
----------------------------- exact H3.
----------------------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H21.
------------------------------ exact H2.
------------------------------ destruct H21 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.Cong B P Q B) /\ (euclidean__axioms.Cong Q B B P)) as H23.
------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (Q) (P) (B) H14).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B P Q B) /\ (euclidean__axioms.Cong Q B B P)) as H24.
-------------------------------- exact H23.
-------------------------------- destruct H24 as [H24 H25].
exact H24.
---------------------------- assert (* Cut *) (euclidean__defs.Lt Q B B A) as H20.
----------------------------- exists P.
split.
------------------------------ exact H18.
------------------------------ exact H19.
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B C) as H21.
------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H21.
------------------------------- exact H3.
------------------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H23.
-------------------------------- exact H2.
-------------------------------- destruct H23 as [H23 H24].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (C) (A) H17).
------------------------------ assert (* Cut *) (euclidean__defs.Lt Q B B C) as H22.
------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H22.
-------------------------------- exact H3.
-------------------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H24.
--------------------------------- exact H2.
--------------------------------- destruct H24 as [H24 H25].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (Q) (B) (B) (A) (B) (C) (H20) H21).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q B B Q) as H23.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H23.
--------------------------------- exact H3.
--------------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H25.
---------------------------------- exact H2.
---------------------------------- destruct H25 as [H25 H26].
apply (@euclidean__axioms.cn__equalityreverse (Q) B).
-------------------------------- assert (* Cut *) (euclidean__defs.Lt B Q B C) as H24.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H24.
---------------------------------- exact H3.
---------------------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H26.
----------------------------------- exact H2.
----------------------------------- destruct H26 as [H26 H27].
apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (Q) (B) (B) (C) (B) (Q) (H22) H23).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H25.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H25.
----------------------------------- exact H3.
----------------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H27.
------------------------------------ exact H2.
------------------------------------ destruct H27 as [H27 H28].
apply (@euclidean__axioms.cn__congruencereflexive (B) C).
---------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H26.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H26.
------------------------------------ exact H3.
------------------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H28.
------------------------------------- exact H2.
------------------------------------- destruct H28 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H30.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (C) H28).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C))) as H31.
--------------------------------------- exact H30.
--------------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)) as H33.
---------------------------------------- exact H32.
---------------------------------------- destruct H33 as [H33 H34].
exact H31.
----------------------------------- assert (* Cut *) (exists (H27: euclidean__axioms.Point), (euclidean__axioms.BetS B H27 C) /\ (euclidean__axioms.Cong B H27 B Q)) as H27.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H27.
------------------------------------- exact H3.
------------------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H29.
-------------------------------------- exact H2.
-------------------------------------- destruct H29 as [H29 H30].
exact H24.
------------------------------------ assert (exists H28: euclidean__axioms.Point, ((euclidean__axioms.BetS B H28 C) /\ (euclidean__axioms.Cong B H28 B Q))) as H29.
------------------------------------- exact H27.
------------------------------------- destruct H29 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.BetS B H28 C) /\ (euclidean__axioms.Cong B H28 B Q)) as H30.
-------------------------------------- exact H29.
-------------------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H32.
--------------------------------------- exact H3.
--------------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H34.
---------------------------------------- exact H2.
---------------------------------------- destruct H34 as [H34 H35].
assert (* Cut *) (euclidean__axioms.BetS P B C) as H36.
----------------------------------------- apply (@lemma__3__6a.lemma__3__6a (A) (P) (B) (C) (H13) H34).
----------------------------------------- assert (* Cut *) (euclidean__defs.Out B C Q) as H37.
------------------------------------------ exists P.
split.
------------------------------------------- exact H32.
------------------------------------------- exact H36.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C H28) as H38.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (H28)).
--------------------------------------------left.
exact H30.

-------------------------------------------- exact H26.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B H28) as H39.
-------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (H28) (Q) H31).
-------------------------------------------- assert (* Cut *) (Q = H28) as H40.
--------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (B) (C) (Q) (H28) (H37) (H38) H39).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B Q C) as H41.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H28 (fun Q0: euclidean__axioms.Point => (euclidean__defs.Midpoint P B Q0) -> ((euclidean__axioms.BetS P B Q0) -> ((euclidean__axioms.Cong P B B Q0) -> ((euclidean__axioms.Cong B Q0 P B) -> ((euclidean__axioms.Cong B Q0 B P) -> ((euclidean__axioms.Cong B P Q0 B) -> ((euclidean__defs.Lt Q0 B B A) -> ((euclidean__defs.Lt Q0 B B C) -> ((euclidean__axioms.Cong Q0 B B Q0) -> ((euclidean__defs.Lt B Q0 B C) -> ((euclidean__axioms.Cong B H28 B Q0) -> ((euclidean__defs.Out B C Q0) -> ((euclidean__axioms.Cong B Q0 B H28) -> (euclidean__axioms.BetS B Q0 C))))))))))))))) with (x := Q).
-----------------------------------------------intro H41.
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
intro H53.
exact H30.

----------------------------------------------- exact H40.
----------------------------------------------- exact H0.
----------------------------------------------- exact H32.
----------------------------------------------- exact H33.
----------------------------------------------- exact H14.
----------------------------------------------- exact H15.
----------------------------------------------- exact H19.
----------------------------------------------- exact H20.
----------------------------------------------- exact H22.
----------------------------------------------- exact H23.
----------------------------------------------- exact H24.
----------------------------------------------- exact H31.
----------------------------------------------- exact H37.
----------------------------------------------- exact H39.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B P A) as H42.
----------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H28 (fun Q0: euclidean__axioms.Point => (euclidean__defs.Midpoint P B Q0) -> ((euclidean__axioms.BetS P B Q0) -> ((euclidean__axioms.Cong P B B Q0) -> ((euclidean__axioms.Cong B Q0 P B) -> ((euclidean__axioms.Cong B Q0 B P) -> ((euclidean__axioms.Cong B P Q0 B) -> ((euclidean__defs.Lt Q0 B B A) -> ((euclidean__defs.Lt Q0 B B C) -> ((euclidean__axioms.Cong Q0 B B Q0) -> ((euclidean__defs.Lt B Q0 B C) -> ((euclidean__axioms.Cong B H28 B Q0) -> ((euclidean__defs.Out B C Q0) -> ((euclidean__axioms.Cong B Q0 B H28) -> ((euclidean__axioms.BetS B Q0 C) -> (euclidean__axioms.BetS B P A)))))))))))))))) with (x := Q).
------------------------------------------------intro H42.
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
intro H53.
intro H54.
intro H55.
exact H18.

------------------------------------------------ exact H40.
------------------------------------------------ exact H0.
------------------------------------------------ exact H32.
------------------------------------------------ exact H33.
------------------------------------------------ exact H14.
------------------------------------------------ exact H15.
------------------------------------------------ exact H19.
------------------------------------------------ exact H20.
------------------------------------------------ exact H22.
------------------------------------------------ exact H23.
------------------------------------------------ exact H24.
------------------------------------------------ exact H31.
------------------------------------------------ exact H37.
------------------------------------------------ exact H39.
------------------------------------------------ exact H41.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H43.
------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (Q) (P) H15).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong P A Q C) as H44.
------------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (B) (P) (A) (B) (Q) (C) (H43) (H21) (H42) H41).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H45.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A P C Q) /\ ((euclidean__axioms.Cong A P Q C) /\ (euclidean__axioms.Cong P A C Q))) as H45.
--------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (P) (A) (Q) (C) H44).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A P C Q) /\ ((euclidean__axioms.Cong A P Q C) /\ (euclidean__axioms.Cong P A C Q))) as H46.
---------------------------------------------------- exact H45.
---------------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Cong A P Q C) /\ (euclidean__axioms.Cong P A C Q)) as H48.
----------------------------------------------------- exact H47.
----------------------------------------------------- destruct H48 as [H48 H49].
exact H46.
-------------------------------------------------- exact H45.
---------- exact H8.
-------- assert (* Cut *) (euclidean__defs.CongA A B P Q B C) as H7.
--------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H7.
---------- exact H3.
---------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H9.
----------- exact H2.
----------- destruct H9 as [H9 H10].
apply (@proposition__15.proposition__15a (A) (C) (P) (Q) (B) (H9) (H7) H6).
--------- assert (* Cut *) (euclidean__axioms.nCol Q B C) as H8.
---------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H8.
----------- exact H3.
----------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H10.
------------ exact H2.
------------ destruct H10 as [H10 H11].
apply (@euclidean__tactics.nCol__notCol (Q) (B) (C)).
-------------apply (@euclidean__tactics.nCol__not__Col (Q) (B) (C)).
--------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (P) (Q) (B) (C) H7).


---------- assert (* Cut *) (euclidean__defs.CongA Q B C C B Q) as H9.
----------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H9.
------------ exact H3.
------------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H11.
------------- exact H2.
------------- destruct H11 as [H11 H12].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (Q) (B) (C) H8).
----------- assert (* Cut *) (euclidean__defs.CongA A B P C B Q) as H10.
------------ assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H10.
------------- exact H3.
------------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H12.
-------------- exact H2.
-------------- destruct H12 as [H12 H13].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (P) (Q) (B) (C) (C) (B) (Q) (H7) H9).
------------ assert (* Cut *) (euclidean__axioms.Cong B A B C) as H11.
------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H11.
-------------- exact H3.
-------------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H13.
--------------- exact H2.
--------------- destruct H13 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H15.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (B) (C) H14).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H16.
----------------- exact H15.
----------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B)) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
exact H18.
------------- assert (* Cut *) (euclidean__axioms.Cong B P B Q) as H12.
-------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H12.
--------------- exact H3.
--------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H14.
---------------- exact H2.
---------------- destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H16.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip (P) (B) (B) (Q) H13).
----------------- assert (* AndElim *) ((euclidean__axioms.Cong B P Q B) /\ ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B))) as H17.
------------------ exact H16.
------------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong B P B Q) /\ (euclidean__axioms.Cong P B Q B)) as H19.
------------------- exact H18.
------------------- destruct H19 as [H19 H20].
exact H19.
-------------- assert (* Cut *) (euclidean__axioms.Cong A P C Q) as H13.
--------------- assert (* AndElim *) ((euclidean__axioms.BetS P B Q) /\ (euclidean__axioms.Cong P B B Q)) as H13.
---------------- exact H3.
---------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A B C) /\ (euclidean__axioms.Cong A B B C)) as H15.
----------------- exact H2.
----------------- destruct H15 as [H15 H16].
assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c) -> ((euclidean__defs.CongA B0 A0 C0 b a c) -> (euclidean__axioms.Cong B0 C0 b c)))) as H17.
------------------ intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c) /\ ((euclidean__defs.CongA A0 B0 C0 a b c) /\ (euclidean__defs.CongA A0 C0 B0 a c b))) as __2.
------------------- apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a) (b) (c) (__) (__0) __1).
------------------- destruct __2 as [__2 __3].
exact __2.
------------------ apply (@H17 (B) (A) (P) (B) (C) (Q) (H11) (H12) H10).
--------------- exact H13.
--- exact H4.
Qed.
