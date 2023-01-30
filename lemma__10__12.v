Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__interior5.
Require Export lemma__linereflectionisometry.
Require Export lemma__rightreverse.
Require Export logic.
Require Export proposition__10.
Definition lemma__10__12 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.Per A B C) -> ((euclidean__defs.Per A B H) -> ((euclidean__axioms.Cong B C B H) -> (euclidean__axioms.Cong A C A H))).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H3.
- exact H0.
- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))))) as H4.
-- exact H3.
-- destruct H4 as [D H4].
assert (* AndElim *) ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)) as H9.
----- exact H8.
----- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__axioms.neq B H) as H11.
------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A H X H) /\ (euclidean__axioms.neq B H)))) as H11.
------- exact H1.
------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A H X H) /\ (euclidean__axioms.neq B H)))) as __TmpHyp.
-------- exact H11.
-------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A H X H) /\ (euclidean__axioms.neq B H))))) as H12.
--------- exact __TmpHyp.
--------- destruct H12 as [x H12].
assert (* AndElim *) ((euclidean__axioms.BetS A B x) /\ ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A H x H) /\ (euclidean__axioms.neq B H)))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A H x H) /\ (euclidean__axioms.neq B H))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong A H x H) /\ (euclidean__axioms.neq B H)) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as H19.
------------- exact H0.
------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as __TmpHyp0.
-------------- exact H19.
-------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C))))) as H20.
--------------- exact __TmpHyp0.
--------------- destruct H20 as [x0 H20].
assert (* AndElim *) ((euclidean__axioms.BetS A B x0) /\ ((euclidean__axioms.Cong A B x0 B) /\ ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C)))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Cong A B x0 B) /\ ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C)) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
exact H18.
------ assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS A B F) /\ ((euclidean__axioms.Cong A B F B) /\ ((euclidean__axioms.Cong A H F H) /\ (euclidean__axioms.neq B H)))) as H12.
------- exact H1.
------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS A B F) /\ ((euclidean__axioms.Cong A B F B) /\ ((euclidean__axioms.Cong A H F H) /\ (euclidean__axioms.neq B H))))) as H13.
-------- exact H12.
-------- destruct H13 as [F H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B F) /\ ((euclidean__axioms.Cong A B F B) /\ ((euclidean__axioms.Cong A H F H) /\ (euclidean__axioms.neq B H)))) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong A B F B) /\ ((euclidean__axioms.Cong A H F H) /\ (euclidean__axioms.neq B H))) as H16.
---------- exact H15.
---------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A H F H) /\ (euclidean__axioms.neq B H)) as H18.
----------- exact H17.
----------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.neq A B) as H20.
------------ assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H20.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (F) H14).
------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H21.
-------------- exact H20.
-------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F)) as H23.
--------------- exact H22.
--------------- destruct H23 as [H23 H24].
exact H23.
------------ assert (* Cut *) (euclidean__axioms.Cong D B A B) as H21.
------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (B) (B) H7).
------------- assert (* Cut *) (euclidean__axioms.Cong D B F B) as H22.
-------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (D) (B) (A) (B) (F) (B) (H21) H16).
-------------- assert (* Cut *) (euclidean__axioms.Cong B F B D) as H23.
--------------- assert (* Cut *) ((euclidean__axioms.Cong B F B D) /\ (euclidean__axioms.Cong B D B F)) as H23.
---------------- apply (@lemma__doublereverse.lemma__doublereverse (D) (B) (F) (B) H22).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong B F B D) /\ (euclidean__axioms.Cong B D B F)) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
exact H24.
--------------- assert (* Cut *) (F = D) as H24.
---------------- apply (@lemma__extensionunique.lemma__extensionunique (A) (B) (F) (D) (H14) (H5) H23).
---------------- assert (* Cut *) (euclidean__axioms.Cong A H D H) as H25.
----------------- apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS A B F0) -> ((euclidean__axioms.Cong A B F0 B) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong D B F0 B) -> ((euclidean__axioms.Cong B F0 B D) -> (euclidean__axioms.Cong A H D H))))))) with (x := F).
------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
exact H27.

------------------ exact H24.
------------------ exact H14.
------------------ exact H16.
------------------ exact H18.
------------------ exact H22.
------------------ exact H23.
----------------- assert (* Cut *) (euclidean__axioms.Cong A C A H) as H26.
------------------ assert (* Cut *) ((C = H) \/ (euclidean__axioms.neq C H)) as H26.
------------------- apply (@euclidean__tactics.eq__or__neq (C) H).
------------------- assert (* Cut *) ((C = H) \/ (euclidean__axioms.neq C H)) as H27.
-------------------- exact H26.
-------------------- assert (* Cut *) ((C = H) \/ (euclidean__axioms.neq C H)) as __TmpHyp.
--------------------- exact H27.
--------------------- assert (C = H \/ euclidean__axioms.neq C H) as H28.
---------------------- exact __TmpHyp.
---------------------- destruct H28 as [H28|H28].
----------------------- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H29.
------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) C).
------------------------ assert (* Cut *) (euclidean__axioms.Cong A C A H) as H30.
------------------------- apply (@eq__ind__r euclidean__axioms.Point H (fun C0: euclidean__axioms.Point => (euclidean__defs.Per A B C0) -> ((euclidean__axioms.Cong B C0 B H) -> ((euclidean__axioms.Cong A C0 D C0) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Cong A C0 A C0) -> (euclidean__axioms.Cong A C0 A H))))))) with (x := C).
--------------------------intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS A B F0) -> ((euclidean__axioms.Cong A B F0 B) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong D B F0 B) -> ((euclidean__axioms.Cong B F0 B D) -> (euclidean__axioms.Cong A H A H))))))) with (x := F).
---------------------------intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
exact H34.

--------------------------- exact H24.
--------------------------- exact H14.
--------------------------- exact H16.
--------------------------- exact H18.
--------------------------- exact H22.
--------------------------- exact H23.

-------------------------- exact H28.
-------------------------- exact H0.
-------------------------- exact H2.
-------------------------- exact H9.
-------------------------- exact H10.
-------------------------- exact H29.
------------------------- exact H30.
----------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS C M H) /\ (euclidean__axioms.Cong M C M H)) as H29.
------------------------ apply (@proposition__10.proposition__10 (C) (H) H28).
------------------------ assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS C M H) /\ (euclidean__axioms.Cong M C M H))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [M H30].
assert (* AndElim *) ((euclidean__axioms.BetS C M H) /\ (euclidean__axioms.Cong M C M H)) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* Cut *) (euclidean__axioms.Cong C B H B) as H33.
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong H B C B) /\ (euclidean__axioms.Cong C B H B)) as H33.
---------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (C) (B) (H) H2).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H B C B) /\ (euclidean__axioms.Cong C B H B)) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
exact H35.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A H) as H34.
---------------------------- assert (* Cut *) ((B = M) \/ (euclidean__axioms.neq B M)) as H34.
----------------------------- apply (@euclidean__tactics.eq__or__neq (B) M).
----------------------------- assert (* Cut *) ((B = M) \/ (euclidean__axioms.neq B M)) as H35.
------------------------------ exact H34.
------------------------------ assert (* Cut *) ((B = M) \/ (euclidean__axioms.neq B M)) as __TmpHyp0.
------------------------------- exact H35.
------------------------------- assert (B = M \/ euclidean__axioms.neq B M) as H36.
-------------------------------- exact __TmpHyp0.
-------------------------------- destruct H36 as [H36|H36].
--------------------------------- assert (* Cut *) (euclidean__defs.Per C B A) as H37.
---------------------------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (C) H0).
---------------------------------- assert (* Cut *) (euclidean__axioms.BetS C B H) as H38.
----------------------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun B0: euclidean__axioms.Point => (euclidean__defs.Per A B0 C) -> ((euclidean__defs.Per A B0 H) -> ((euclidean__axioms.Cong B0 C B0 H) -> ((euclidean__axioms.BetS A B0 D) -> ((euclidean__axioms.Cong A B0 D B0) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.neq B0 H) -> ((euclidean__axioms.BetS A B0 F) -> ((euclidean__axioms.Cong A B0 F B0) -> ((euclidean__axioms.neq B0 H) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong D B0 A B0) -> ((euclidean__axioms.Cong D B0 F B0) -> ((euclidean__axioms.Cong B0 F B0 D) -> ((euclidean__axioms.Cong C B0 H B0) -> ((euclidean__defs.Per C B0 A) -> (euclidean__axioms.BetS C B0 H)))))))))))))))))) with (x := B).
------------------------------------intro H38.
intro H39.
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
intro H51.
intro H52.
intro H53.
apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.Cong A M F0 M) -> ((euclidean__axioms.BetS A M F0) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong M F0 M D) -> ((euclidean__axioms.Cong D M F0 M) -> (euclidean__axioms.BetS C M H))))))) with (x := F).
-------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H31.

------------------------------------- exact H24.
------------------------------------- exact H46.
------------------------------------- exact H45.
------------------------------------- exact H18.
------------------------------------- exact H51.
------------------------------------- exact H50.

------------------------------------ exact H36.
------------------------------------ exact H0.
------------------------------------ exact H1.
------------------------------------ exact H2.
------------------------------------ exact H5.
------------------------------------ exact H7.
------------------------------------ exact H10.
------------------------------------ exact H11.
------------------------------------ exact H14.
------------------------------------ exact H16.
------------------------------------ exact H19.
------------------------------------ exact H20.
------------------------------------ exact H21.
------------------------------------ exact H22.
------------------------------------ exact H23.
------------------------------------ exact H33.
------------------------------------ exact H37.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B H) as H39.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point M (fun B0: euclidean__axioms.Point => (euclidean__defs.Per A B0 C) -> ((euclidean__defs.Per A B0 H) -> ((euclidean__axioms.Cong B0 C B0 H) -> ((euclidean__axioms.BetS A B0 D) -> ((euclidean__axioms.Cong A B0 D B0) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.neq B0 H) -> ((euclidean__axioms.BetS A B0 F) -> ((euclidean__axioms.Cong A B0 F B0) -> ((euclidean__axioms.neq B0 H) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Cong D B0 A B0) -> ((euclidean__axioms.Cong D B0 F B0) -> ((euclidean__axioms.Cong B0 F B0 D) -> ((euclidean__axioms.Cong C B0 H B0) -> ((euclidean__defs.Per C B0 A) -> ((euclidean__axioms.BetS C B0 H) -> (euclidean__axioms.Cong B0 C B0 H))))))))))))))))))) with (x := B).
-------------------------------------intro H39.
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
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.Cong A M F0 M) -> ((euclidean__axioms.BetS A M F0) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong M F0 M D) -> ((euclidean__axioms.Cong D M F0 M) -> (euclidean__axioms.Cong M C M H))))))) with (x := F).
--------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
exact H32.

-------------------------------------- exact H24.
-------------------------------------- exact H47.
-------------------------------------- exact H46.
-------------------------------------- exact H18.
-------------------------------------- exact H52.
-------------------------------------- exact H51.

------------------------------------- exact H36.
------------------------------------- exact H0.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H5.
------------------------------------- exact H7.
------------------------------------- exact H10.
------------------------------------- exact H11.
------------------------------------- exact H14.
------------------------------------- exact H16.
------------------------------------- exact H19.
------------------------------------- exact H20.
------------------------------------- exact H21.
------------------------------------- exact H22.
------------------------------------- exact H23.
------------------------------------- exact H33.
------------------------------------- exact H37.
------------------------------------- exact H38.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C B B H) as H40.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C B H B) /\ ((euclidean__axioms.Cong C B B H) /\ (euclidean__axioms.Cong B C H B))) as H40.
-------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (B) (H) H39).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B H B) /\ ((euclidean__axioms.Cong C B B H) /\ (euclidean__axioms.Cong B C H B))) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Cong C B B H) /\ (euclidean__axioms.Cong B C H B)) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
exact H43.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A H A) as H41.
-------------------------------------- apply (@lemma__rightreverse.lemma__rightreverse (C) (B) (A) (H) (H37) (H38) H40).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A H) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C A H) /\ ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H))) as H42.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (H) (A) H41).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C A H) /\ ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H))) as H43.
----------------------------------------- exact H42.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H)) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
exact H43.
--------------------------------------- exact H42.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq M B) as H37.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (M) H36).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong C M H M) as H38.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M H M) /\ ((euclidean__axioms.Cong C M M H) /\ (euclidean__axioms.Cong M C H M))) as H38.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (M) (C) (M) (H) H32).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C M H M) /\ ((euclidean__axioms.Cong C M M H) /\ (euclidean__axioms.Cong M C H M))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong C M M H) /\ (euclidean__axioms.Cong M C H M)) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
exact H39.
----------------------------------- assert (* Cut *) (euclidean__defs.Per C M B) as H39.
------------------------------------ exists H.
split.
------------------------------------- exact H31.
------------------------------------- split.
-------------------------------------- exact H38.
-------------------------------------- split.
--------------------------------------- exact H33.
--------------------------------------- exact H37.
------------------------------------ assert (* Cut *) (euclidean__defs.Per B M C) as H40.
------------------------------------- apply (@lemma__8__2.lemma__8__2 (C) (M) (B) H39).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A C D) as H41.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H41.
--------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (D) (C) H9).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C A C D) /\ ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong C A D C) /\ (euclidean__axioms.Cong A C C D)) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
exact H42.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H A H D) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H A H D) /\ ((euclidean__axioms.Cong H A D H) /\ (euclidean__axioms.Cong A H H D))) as H42.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (H) (D) (H) H25).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H A H D) /\ ((euclidean__axioms.Cong H A D H) /\ (euclidean__axioms.Cong A H H D))) as H43.
----------------------------------------- exact H42.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong H A D H) /\ (euclidean__axioms.Cong A H H D)) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
exact H43.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C M C M) as H43.
---------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (C) M).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M H M H) as H44.
----------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (M) H).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M A M D) as H45.
------------------------------------------ apply (@lemma__interior5.lemma__interior5 (C) (M) (H) (A) (C) (M) (H) (D) (H31) (H31) (H43) (H44) (H41) H42).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A M D M) as H46.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A M D M) /\ ((euclidean__axioms.Cong A M M D) /\ (euclidean__axioms.Cong M A D M))) as H46.
-------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (A) (M) (D) H45).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A M D M) /\ ((euclidean__axioms.Cong A M M D) /\ (euclidean__axioms.Cong M A D M))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong A M M D) /\ (euclidean__axioms.Cong M A D M)) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
exact H47.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B M) as H47.
-------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS A B F0) -> ((euclidean__axioms.Cong A B F0 B) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong D B F0 B) -> ((euclidean__axioms.Cong B F0 B D) -> (euclidean__axioms.neq B M))))))) with (x := F).
---------------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
exact H36.

--------------------------------------------- exact H24.
--------------------------------------------- exact H14.
--------------------------------------------- exact H16.
--------------------------------------------- exact H18.
--------------------------------------------- exact H22.
--------------------------------------------- exact H23.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B M) as H48.
--------------------------------------------- exists D.
split.
---------------------------------------------- exact H5.
---------------------------------------------- split.
----------------------------------------------- exact H7.
----------------------------------------------- split.
------------------------------------------------ exact H46.
------------------------------------------------ exact H47.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B D) as H49.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A B D) /\ ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D))) as H49.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (B) H7).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A B D) /\ ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D))) as H50.
------------------------------------------------ exact H49.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D)) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52 H53].
exact H50.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Per M B A) as H50.
----------------------------------------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (M) H48).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A H D) as H51.
------------------------------------------------ apply (@lemma__linereflectionisometry.lemma__linereflectionisometry (M) (B) (C) (A) (H) (D) (H40) (H50) (H31) (H5) (H32) H49).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A C D H) as H52.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C D H) /\ ((euclidean__axioms.Cong A C H D) /\ (euclidean__axioms.Cong C A D H))) as H52.
-------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (H) (D) H51).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C D H) /\ ((euclidean__axioms.Cong A C H D) /\ (euclidean__axioms.Cong C A D H))) as H53.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong A C H D) /\ (euclidean__axioms.Cong C A D H)) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
exact H53.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D B A) as H53.
-------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (D) H5).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D B A) as H54.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D B A) /\ ((euclidean__axioms.Cong B D A B) /\ (euclidean__axioms.Cong D B B A))) as H54.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (A) (B) H21).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D B A) /\ ((euclidean__axioms.Cong B D A B) /\ (euclidean__axioms.Cong D B B A))) as H55.
----------------------------------------------------- exact H54.
----------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong B D A B) /\ (euclidean__axioms.Cong D B B A)) as H57.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H57 as [H57 H58].
exact H55.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B D) as H55.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A B B D) /\ (euclidean__axioms.Cong B A D B))) as H55.
----------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (A) (B) (D) H49).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A B B D) /\ (euclidean__axioms.Cong B A D B))) as H56.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Cong A B B D) /\ (euclidean__axioms.Cong B A D B)) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [H58 H59].
exact H58.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A H D H) as H56.
----------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS A B F0) -> ((euclidean__axioms.Cong A B F0 B) -> ((euclidean__axioms.Cong A H F0 H) -> ((euclidean__axioms.Cong D B F0 B) -> ((euclidean__axioms.Cong B F0 B D) -> (euclidean__axioms.Cong A H D H))))))) with (x := F).
------------------------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
exact H25.

------------------------------------------------------ exact H24.
------------------------------------------------------ exact H14.
------------------------------------------------------ exact H16.
------------------------------------------------------ exact H18.
------------------------------------------------------ exact H22.
------------------------------------------------------ exact H23.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D H A H) as H57.
------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (A) (H) (H) H56).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C A H D) as H58.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H D H A) /\ ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A))) as H58.
-------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (H) (A) (H) H57).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H D H A) /\ ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A))) as H59.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A)) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
exact H51.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H D H A) as H59.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H D H A) /\ ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A))) as H59.
--------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (H) (A) (H) H57).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H D H A) /\ ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A))) as H60.
---------------------------------------------------------- exact H59.
---------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Cong H D A H) /\ (euclidean__axioms.Cong D H H A)) as H62.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- destruct H62 as [H62 H63].
exact H60.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A H A) as H60.
--------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (A) (H) (D) (H) (A) (H58) H59).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A H) as H61.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A C A H) /\ ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H))) as H61.
----------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (H) (A) H60).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A C A H) /\ ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H))) as H62.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Cong A C H A) /\ (euclidean__axioms.Cong C A A H)) as H64.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- destruct H64 as [H64 H65].
exact H62.
---------------------------------------------------------- exact H61.
---------------------------- exact H34.
------------------ exact H26.
Qed.
