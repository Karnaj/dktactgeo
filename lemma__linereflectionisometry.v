Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__NCdistinct.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__pointreflectionisometry.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export lemma__rightreverse.
Require Export logic.
Require Export proposition__10.
Definition lemma__linereflectionisometry : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Per B A C) -> ((euclidean__defs.Per A B D) -> ((euclidean__axioms.BetS C A E) -> ((euclidean__axioms.BetS D B F) -> ((euclidean__axioms.Cong A C A E) -> ((euclidean__axioms.Cong B D B F) -> (euclidean__axioms.Cong C D E F)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (exists (H5: euclidean__axioms.Point), (euclidean__axioms.BetS B A H5) /\ ((euclidean__axioms.Cong B A H5 A) /\ ((euclidean__axioms.Cong B C H5 C) /\ (euclidean__axioms.neq A C)))) as H5.
- exact H.
- assert (exists H6: euclidean__axioms.Point, ((euclidean__axioms.BetS B A H6) /\ ((euclidean__axioms.Cong B A H6 A) /\ ((euclidean__axioms.Cong B C H6 C) /\ (euclidean__axioms.neq A C))))) as H7.
-- exact H5.
-- destruct H7 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.BetS B A H6) /\ ((euclidean__axioms.Cong B A H6 A) /\ ((euclidean__axioms.Cong B C H6 C) /\ (euclidean__axioms.neq A C)))) as H8.
--- exact H7.
--- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Cong B A H6 A) /\ ((euclidean__axioms.Cong B C H6 C) /\ (euclidean__axioms.neq A C))) as H10.
---- exact H9.
---- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Cong B C H6 C) /\ (euclidean__axioms.neq A C)) as H12.
----- exact H11.
----- destruct H12 as [H12 H13].
assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS A B G) /\ ((euclidean__axioms.Cong A B G B) /\ ((euclidean__axioms.Cong A D G D) /\ (euclidean__axioms.neq B D)))) as H14.
------ exact H0.
------ assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS A B G) /\ ((euclidean__axioms.Cong A B G B) /\ ((euclidean__axioms.Cong A D G D) /\ (euclidean__axioms.neq B D))))) as H15.
------- exact H14.
------- destruct H15 as [G H15].
assert (* AndElim *) ((euclidean__axioms.BetS A B G) /\ ((euclidean__axioms.Cong A B G B) /\ ((euclidean__axioms.Cong A D G D) /\ (euclidean__axioms.neq B D)))) as H16.
-------- exact H15.
-------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A B G B) /\ ((euclidean__axioms.Cong A D G D) /\ (euclidean__axioms.neq B D))) as H18.
--------- exact H17.
--------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong A D G D) /\ (euclidean__axioms.neq B D)) as H20.
---------- exact H19.
---------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.neq A B) as H22.
----------- assert (* Cut *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A G))) as H22.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (G) H16).
------------ assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A G))) as H23.
------------- exact H22.
------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A G)) as H25.
-------------- exact H24.
-------------- destruct H25 as [H25 H26].
exact H25.
----------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M B) /\ (euclidean__axioms.Cong M A M B)) as H23.
------------ apply (@proposition__10.proposition__10 (A) (B) H22).
------------ assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M B) /\ (euclidean__axioms.Cong M A M B))) as H24.
------------- exact H23.
------------- destruct H24 as [M H24].
assert (* AndElim *) ((euclidean__axioms.BetS A M B) /\ (euclidean__axioms.Cong M A M B)) as H25.
-------------- exact H24.
-------------- destruct H25 as [H25 H26].
assert (* Cut *) (euclidean__defs.Per D B A) as H27.
--------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (D) H0).
--------------- assert (* Cut *) (euclidean__axioms.neq B A) as H28.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H22).
---------------- assert (* Cut *) (euclidean__axioms.BetS B M A) as H29.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (B) H25).
----------------- assert (* Cut *) (euclidean__defs.Out B A M) as H30.
------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (M)).
-------------------left.
exact H29.

------------------- exact H28.
------------------ assert (* Cut *) (euclidean__defs.Per D B M) as H31.
------------------- apply (@lemma__8__3.lemma__8__3 (D) (B) (A) (M) (H27) H30).
------------------- assert (* Cut *) (euclidean__axioms.nCol D B M) as H32.
-------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (D) (B) (M) H31).
-------------------- assert (* Cut *) (~(D = M)) as H33.
--------------------- intro H33.
assert (* Cut *) (euclidean__axioms.Col D B M) as H34.
---------------------- right.
left.
exact H33.
---------------------- apply (@euclidean__tactics.Col__nCol__False (D) (B) (M) (H32) H34).
--------------------- assert (* Cut *) (euclidean__axioms.neq M D) as H34.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (M) H33).
---------------------- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS D M R) /\ (euclidean__axioms.Cong M R M D)) as H35.
----------------------- apply (@lemma__extension.lemma__extension (D) (M) (M) (D) (H33) H34).
----------------------- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS D M R) /\ (euclidean__axioms.Cong M R M D))) as H36.
------------------------ exact H35.
------------------------ destruct H36 as [R H36].
assert (* AndElim *) ((euclidean__axioms.BetS D M R) /\ (euclidean__axioms.Cong M R M D)) as H37.
------------------------- exact H36.
------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (euclidean__axioms.Cong D B B F) as H39.
-------------------------- assert (* Cut *) ((euclidean__axioms.Cong D B F B) /\ ((euclidean__axioms.Cong D B B F) /\ (euclidean__axioms.Cong B D F B))) as H39.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (D) (B) (F) H4).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D B F B) /\ ((euclidean__axioms.Cong D B B F) /\ (euclidean__axioms.Cong B D F B))) as H40.
---------------------------- exact H39.
---------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong D B B F) /\ (euclidean__axioms.Cong B D F B)) as H42.
----------------------------- exact H41.
----------------------------- destruct H42 as [H42 H43].
exact H42.
-------------------------- assert (* Cut *) (euclidean__axioms.Col D B F) as H40.
--------------------------- right.
right.
right.
right.
left.
exact H2.
--------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H41.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H41.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (B) (F) H2).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F)) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
exact H42.
---------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H42.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (F) H41).
----------------------------- assert (* Cut *) (euclidean__defs.Per D B A) as H43.
------------------------------ exact H27.
------------------------------ assert (* Cut *) (euclidean__defs.Per F B A) as H44.
------------------------------- apply (@lemma__collinearright.lemma__collinearright (D) (B) (F) (A) (H43) (H40) H42).
------------------------------- assert (* Cut *) (euclidean__defs.Per F B M) as H45.
-------------------------------- apply (@lemma__8__3.lemma__8__3 (F) (B) (A) (M) (H44) H30).
-------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B M) as H46.
--------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (F) (B) (M) H45).
--------------------------------- assert (* Cut *) (~(F = M)) as H47.
---------------------------------- intro H47.
assert (* Cut *) (euclidean__axioms.Col F B M) as H48.
----------------------------------- right.
left.
exact H47.
----------------------------------- apply (@euclidean__tactics.Col__nCol__False (F) (B) (M) (H46) H48).
---------------------------------- assert (* Cut *) (euclidean__axioms.neq M F) as H48.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (M) H47).
----------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS F M Q) /\ (euclidean__axioms.Cong M Q M F)) as H49.
------------------------------------ apply (@lemma__extension.lemma__extension (F) (M) (M) (F) (H47) H48).
------------------------------------ assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS F M Q) /\ (euclidean__axioms.Cong M Q M F))) as H50.
------------------------------------- exact H49.
------------------------------------- destruct H50 as [Q H50].
assert (* AndElim *) ((euclidean__axioms.BetS F M Q) /\ (euclidean__axioms.Cong M Q M F)) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
assert (* Cut *) (euclidean__axioms.Cong M D M R) as H53.
--------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (M) (R) (D) H38).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D M M R) as H54.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D M R M) /\ ((euclidean__axioms.Cong D M M R) /\ (euclidean__axioms.Cong M D R M))) as H54.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (D) (M) (R) H53).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D M R M) /\ ((euclidean__axioms.Cong D M M R) /\ (euclidean__axioms.Cong M D R M))) as H55.
------------------------------------------ exact H54.
------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Cong D M M R) /\ (euclidean__axioms.Cong M D R M)) as H57.
------------------------------------------- exact H56.
------------------------------------------- destruct H57 as [H57 H58].
exact H57.
---------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint D M R) as H55.
----------------------------------------- split.
------------------------------------------ exact H37.
------------------------------------------ exact H54.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M F M Q) as H56.
------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (M) (Q) (F) H52).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F M M Q) as H57.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F M Q M) /\ ((euclidean__axioms.Cong F M M Q) /\ (euclidean__axioms.Cong M F Q M))) as H57.
-------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (F) (M) (Q) H56).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F M Q M) /\ ((euclidean__axioms.Cong F M M Q) /\ (euclidean__axioms.Cong M F Q M))) as H58.
--------------------------------------------- exact H57.
--------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Cong F M M Q) /\ (euclidean__axioms.Cong M F Q M)) as H60.
---------------------------------------------- exact H59.
---------------------------------------------- destruct H60 as [H60 H61].
exact H60.
------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint F M Q) as H58.
-------------------------------------------- split.
--------------------------------------------- exact H51.
--------------------------------------------- exact H57.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M B M A) as H59.
--------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (M) (A) (B) H26).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B M M A) as H60.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B M A M) /\ ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M))) as H60.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (B) (M) (A) H59).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B M A M) /\ ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M))) as H61.
------------------------------------------------ exact H60.
------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M)) as H63.
------------------------------------------------- exact H62.
------------------------------------------------- destruct H63 as [H63 H64].
exact H63.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M A) as H61.
----------------------------------------------- exact H29.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint B M A) as H62.
------------------------------------------------ split.
------------------------------------------------- exact H61.
------------------------------------------------- exact H60.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F B Q A) as H63.
------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry (F) (M) (Q) (B) (A) (H58) (H62) H42).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F F B) as H64.
-------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (B) F).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D F B) as H65.
--------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (D) (B) (F) (F) (B) (H4) H64).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per C A B) as H66.
---------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (B) (A) (C) H).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A B M) as H67.
----------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (B) (M)).
------------------------------------------------------left.
exact H25.

------------------------------------------------------ exact H22.
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Per C A M) as H68.
------------------------------------------------------ apply (@lemma__8__3.lemma__8__3 (C) (A) (B) (M) (H66) H67).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS Q M F) as H69.
------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (M) (Q) H51).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS R M D) as H70.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (M) (R) H37).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D B B F) as H71.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D B B F) /\ ((euclidean__axioms.Cong D B F B) /\ (euclidean__axioms.Cong B D B F))) as H71.
---------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (D) (F) (B) H65).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D B B F) /\ ((euclidean__axioms.Cong D B F B) /\ (euclidean__axioms.Cong B D B F))) as H72.
----------------------------------------------------------- exact H71.
----------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Cong D B F B) /\ (euclidean__axioms.Cong B D B F)) as H74.
------------------------------------------------------------ exact H73.
------------------------------------------------------------ destruct H74 as [H74 H75].
exact H72.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D M F M) as H72.
---------------------------------------------------------- apply (@lemma__rightreverse.lemma__rightreverse (D) (B) (M) (F) (H31) (H2) H71).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M D M) as H73.
----------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (D) (M) (M) H72).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M M Q) as H74.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H74.
------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (M) (D) (M) H73).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D)) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
exact H57.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong Q M F M) as H75.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong Q M F M) /\ ((euclidean__axioms.Cong Q M M F) /\ (euclidean__axioms.Cong M Q F M))) as H75.
-------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (Q) (M) (F) H52).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q M F M) /\ ((euclidean__axioms.Cong Q M M F) /\ (euclidean__axioms.Cong M Q F M))) as H76.
--------------------------------------------------------------- exact H75.
--------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Cong Q M M F) /\ (euclidean__axioms.Cong M Q F M)) as H78.
---------------------------------------------------------------- exact H77.
---------------------------------------------------------------- destruct H78 as [H78 H79].
exact H76.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q M D M) as H76.
-------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (M) (F) (M) (D) (M) (H75) H73).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q M M R) as H77.
--------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (M) (D) (M) (M) (R) (H76) H54).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q M R M) as H78.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M Q R M) /\ ((euclidean__axioms.Cong M Q M R) /\ (euclidean__axioms.Cong Q M R M))) as H78.
----------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (Q) (M) (M) (R) H77).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M Q R M) /\ ((euclidean__axioms.Cong M Q M R) /\ (euclidean__axioms.Cong Q M R M))) as H79.
------------------------------------------------------------------ exact H78.
------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Cong M Q M R) /\ (euclidean__axioms.Cong Q M R M)) as H81.
------------------------------------------------------------------- exact H80.
------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H82.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M F M D) as H79.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H79.
------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (F) (M) (D) (M) H73).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H80.
------------------------------------------------------------------- exact H79.
------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D)) as H82.
-------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H80.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A A E) as H80.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong C A E A) /\ ((euclidean__axioms.Cong C A A E) /\ (euclidean__axioms.Cong A C E A))) as H80.
------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (A) (E) H3).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C A E A) /\ ((euclidean__axioms.Cong C A A E) /\ (euclidean__axioms.Cong A C E A))) as H81.
-------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Cong C A A E) /\ (euclidean__axioms.Cong A C E A)) as H83.
--------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H83.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C M E M) as H81.
------------------------------------------------------------------- apply (@lemma__rightreverse.lemma__rightreverse (C) (A) (M) (E) (H68) (H1) H80).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E M C M) as H82.
-------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (C) (M) (M) H81).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M E M C) as H83.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M E M C) /\ ((euclidean__axioms.Cong M E C M) /\ (euclidean__axioms.Cong E M M C))) as H83.
---------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (M) (C) (M) H82).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M E M C) /\ ((euclidean__axioms.Cong M E C M) /\ (euclidean__axioms.Cong E M M C))) as H84.
----------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Cong M E C M) /\ (euclidean__axioms.Cong E M M C)) as H86.
------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------ destruct H86 as [H86 H87].
exact H84.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint D M R) as H84.
---------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint F M Q) as H85.
----------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M B M A) as H86.
------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B M M A) as H87.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B M A M) /\ ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M))) as H87.
-------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (M) (B) (M) (A) H86).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B M A M) /\ ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M))) as H88.
--------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Cong B M M A) /\ (euclidean__axioms.Cong M B A M)) as H90.
---------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H90.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint B M A) as H88.
-------------------------------------------------------------------------- exact H62.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B Q A) as H89.
--------------------------------------------------------------------------- exact H63.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B A) as H90.
---------------------------------------------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (D) (B) (A) H43).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H91.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)))))) as H91.
------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (A) H90).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)))))) as H92.
------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))))) as H94.
-------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)))) as H96.
--------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H98.
---------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)) as H100.
----------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H92.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D B R A) as H92.
------------------------------------------------------------------------------ apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry (D) (M) (R) (B) (A) (H84) (H88) H91).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong Q A F B) as H93.
------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (Q) (F) (B) (A) H89).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F D B) as H94.
-------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (D) (B) (F) H71).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B D B) as H95.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F B B D) /\ ((euclidean__axioms.Cong F B D B) /\ (euclidean__axioms.Cong B F B D))) as H95.
---------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (F) (D) (B) H94).
---------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F B B D) /\ ((euclidean__axioms.Cong F B D B) /\ (euclidean__axioms.Cong B F B D))) as H96.
----------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Cong F B D B) /\ (euclidean__axioms.Cong B F B D)) as H98.
------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
exact H98.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q A D B) as H96.
---------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (A) (F) (B) (D) (B) (H93) H95).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q A R A) as H97.
----------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (A) (D) (B) (R) (A) (H96) H92).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q A A R) as H98.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong A Q A R) /\ ((euclidean__axioms.Cong A Q R A) /\ (euclidean__axioms.Cong Q A A R))) as H98.
------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (Q) (A) (R) (A) H97).
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A Q A R) /\ ((euclidean__axioms.Cong A Q R A) /\ (euclidean__axioms.Cong Q A A R))) as H99.
-------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Cong A Q R A) /\ (euclidean__axioms.Cong Q A A R)) as H101.
--------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H102.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D F) as H99.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H99.
-------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (B) (F) H2).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H100.
--------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F)) as H102.
---------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H103.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D F R Q) as H100.
-------------------------------------------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry (D) (M) (R) (F) (Q) (H84) (H85) H99).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D Q R) as H101.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F D Q R) /\ ((euclidean__axioms.Cong F D R Q) /\ (euclidean__axioms.Cong D F Q R))) as H101.
---------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (F) (R) (Q) H100).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F D Q R) /\ ((euclidean__axioms.Cong F D R Q) /\ (euclidean__axioms.Cong D F Q R))) as H102.
----------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Cong F D R Q) /\ (euclidean__axioms.Cong D F Q R)) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
exact H102.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F B D) as H102.
---------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (B) (F) H2).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D A R) as H103.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D A R) /\ ((euclidean__axioms.Cong B D R A) /\ (euclidean__axioms.Cong D B A R))) as H103.
------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (R) (A) H92).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B D A R) /\ ((euclidean__axioms.Cong B D R A) /\ (euclidean__axioms.Cong D B A R))) as H104.
------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Cong B D R A) /\ (euclidean__axioms.Cong D B A R)) as H106.
-------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
exact H104.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS Q A R) as H104.
------------------------------------------------------------------------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (F) (B) (D) (Q) (A) (R) (H89) (H101) (H103) H102).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Midpoint Q A R) as H105.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A A C) as H106.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E A A C) /\ (euclidean__axioms.Cong A C E A)) as H106.
--------------------------------------------------------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (C) (A) (A) (E) H80).
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E A A C) /\ (euclidean__axioms.Cong A C E A)) as H107.
---------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
exact H107.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E A C) as H107.
--------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (A) (E) H1).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint E A C) as H108.
---------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D E F) as H109.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E Q) \/ (E = Q)) as H109.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.neq__or__eq (E) Q).
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E Q) \/ (E = Q)) as H110.
------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E Q) \/ (E = Q)) as __TmpHyp.
-------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq E Q \/ E = Q) as H111.
--------------------------------------------------------------------------------------------------- exact __TmpHyp.
--------------------------------------------------------------------------------------------------- destruct H111 as [H111|H111].
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E Q C R) as H112.
----------------------------------------------------------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry (E) (A) (C) (Q) (R) (H108) (H105) H111).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q E R C) as H113.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong Q E R C) /\ ((euclidean__axioms.Cong Q E C R) /\ (euclidean__axioms.Cong E Q R C))) as H113.
------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (Q) (C) (R) H112).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q E R C) /\ ((euclidean__axioms.Cong Q E C R) /\ (euclidean__axioms.Cong E Q R C))) as H114.
-------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Cong Q E C R) /\ (euclidean__axioms.Cong E Q R C)) as H116.
--------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H114.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E F C D) as H114.
------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__5__line (Q) (M) (F) (E) (R) (M) (D) (C) (H79) (H113) (H83) (H69) (H70) H78).
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D E F) as H115.
-------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (E) (F) (D) H114).
-------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint F M E) as H112.
----------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> (euclidean__defs.Midpoint F M E0))))))))))) with (x := E).
------------------------------------------------------------------------------------------------------intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
exact H85.

------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------------------------ exact H3.
------------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------ exact H108.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H113.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H113.
------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (A) (C) H107).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H114.
-------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C)) as H116.
--------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H42.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F D) as H114.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F D))) as H114.
-------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (B) (D) H102).
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F D))) as H115.
--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F D)) as H117.
---------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H118.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H115.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H115.
--------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (A) (C) H107).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H21.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B E A) as H116.
--------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> (euclidean__axioms.Cong F B E0 A)))))))))))) with (x := E).
----------------------------------------------------------------------------------------------------------intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
exact H89.

---------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D A R) as H117.
---------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> (euclidean__axioms.Cong B D A R))))))))))))) with (x := E).
-----------------------------------------------------------------------------------------------------------intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
exact H103.

----------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------------------------------- exact H3.
----------------------------------------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------------- exact H108.
----------------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D E R) as H118.
----------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> (euclidean__axioms.Cong F D E0 R))))))))))))) with (x := E).
------------------------------------------------------------------------------------------------------------intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
exact H101.

------------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------------------------------ exact H3.
------------------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------------ exact H116.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E A R) as H119.
------------------------------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.Cong F D E0 R) -> (euclidean__axioms.BetS E0 A R)))))))))))))) with (x := E).
-------------------------------------------------------------------------------------------------------------intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
exact H104.

------------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------------- exact H1.
------------------------------------------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E A C) as H120.
------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.Cong F D E0 R) -> ((euclidean__axioms.BetS E0 A R) -> (euclidean__axioms.BetS E0 A C))))))))))))))) with (x := E).
--------------------------------------------------------------------------------------------------------------intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
exact H127.

-------------------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H121.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) C).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A R B D) as H122.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (B) (D) (R) H117).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A R B F) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (R) (B) (D) (B) (F) (H122) H4).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F A E) as H124.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B F A E) /\ ((euclidean__axioms.Cong B F E A) /\ (euclidean__axioms.Cong F B A E))) as H124.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (F) (B) (E) (A) H116).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B F A E) /\ ((euclidean__axioms.Cong B F E A) /\ (euclidean__axioms.Cong F B A E))) as H125.
------------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Cong B F E A) /\ (euclidean__axioms.Cong F B A E)) as H127.
-------------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H125.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A R A E) as H125.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (R) (B) (F) (A) (E) (H123) H124).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A E A C) as H126.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (C) (E) H3).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A R A C) as H127.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (R) (A) (E) (A) (C) (H125) H126).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (R = C) as H128.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__extensionunique.lemma__extensionunique (E) (A) (R) (C) (H119) (H120) H127).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B F) as H129.
---------------------------------------------------------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H130.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H130.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (A) (C) H120).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C))) as H131.
------------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E C)) as H133.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H41.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H131.
------------------------------------------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> (euclidean__axioms.neq F B)))))))))))))))))))))))))) with (x := R).
-------------------------------------------------------------------------------------------------------------------------intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__axioms.neq F B))))))))))))))))))) with (x := E).
--------------------------------------------------------------------------------------------------------------------------intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
exact H113.

-------------------------------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------------------------- exact H150.
-------------------------------------------------------------------------------------------------------------------------- exact H149.
-------------------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------------------- exact H153.
-------------------------------------------------------------------------------------------------------------------------- exact H126.

------------------------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------------------------------------------------- exact H53.
------------------------------------------------------------------------------------------------------------------------- exact H54.
------------------------------------------------------------------------------------------------------------------------- exact H55.
------------------------------------------------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per F B M) as H132.
------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> (euclidean__defs.Per F B M)))))))))))))))))))))))))) with (x := R).
--------------------------------------------------------------------------------------------------------------------------intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__defs.Per F B M))))))))))))))))))) with (x := E).
---------------------------------------------------------------------------------------------------------------------------intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
exact H45.

--------------------------------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------------------------- exact H3.
--------------------------------------------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------------- exact H150.
--------------------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------------- exact H126.

-------------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B B D) as H133.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B F B D) /\ ((euclidean__axioms.Cong B F D B) /\ (euclidean__axioms.Cong F B B D))) as H133.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (B) (D) (B) H95).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B F B D) /\ ((euclidean__axioms.Cong B F D B) /\ (euclidean__axioms.Cong F B B D))) as H134.
---------------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Cong B F D B) /\ (euclidean__axioms.Cong F B B D)) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H137.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M D M) as H134.
--------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> (euclidean__axioms.Cong F M D M)))))))))))))))))))))))))) with (x := R).
----------------------------------------------------------------------------------------------------------------------------intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__axioms.Cong F M D M))))))))))))))))))) with (x := E).
-----------------------------------------------------------------------------------------------------------------------------intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
exact H73.

----------------------------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------------------------------------------------------- exact H3.
----------------------------------------------------------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------------------------------- exact H108.
----------------------------------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------------- exact H152.
----------------------------------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------- exact H126.

---------------------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------------------------------------------------------------- exact H38.
---------------------------------------------------------------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------------------------------------------------------------- exact H54.
---------------------------------------------------------------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------------------------------------------------------------- exact H77.
---------------------------------------------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------------------------------------------- exact H105.
---------------------------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M M D) as H135.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H135.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (M) (D) (M) H134).
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M F M D) /\ ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D))) as H136.
------------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------------ destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Cong M F D M) /\ (euclidean__axioms.Cong F M M D)) as H138.
------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
exact H139.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M M R) as H136.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (M) (M) (D) (M) (R) (H135) H53).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M M C) as H137.
------------------------------------------------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> ((euclidean__axioms.Cong F M M R0) -> (euclidean__axioms.Cong F M M C))))))))))))))))))))))))))) with (x := R).
-------------------------------------------------------------------------------------------------------------------------------intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__axioms.Cong F M M C))))))))))))))))))) with (x := E).
--------------------------------------------------------------------------------------------------------------------------------intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
exact H161.

-------------------------------------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------- exact H155.
-------------------------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------------------------- exact H159.
-------------------------------------------------------------------------------------------------------------------------------- exact H126.

------------------------------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------------------------------------------------------- exact H53.
------------------------------------------------------------------------------------------------------------------------------- exact H54.
------------------------------------------------------------------------------------------------------------------------------- exact H55.
------------------------------------------------------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------------------------- exact H125.
------------------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D M F M) as H138.
------------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> ((euclidean__axioms.Cong F M M R0) -> (euclidean__axioms.Cong D M F M))))))))))))))))))))))))))) with (x := R).
--------------------------------------------------------------------------------------------------------------------------------intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__axioms.Cong D M F M))))))))))))))))))) with (x := E).
---------------------------------------------------------------------------------------------------------------------------------intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
exact H72.

--------------------------------------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------------------------------- exact H3.
--------------------------------------------------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------------------- exact H157.
--------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------------------- exact H160.
--------------------------------------------------------------------------------------------------------------------------------- exact H126.

-------------------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M M E) as H139.
-------------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> ((euclidean__axioms.Cong F M M R0) -> (euclidean__axioms.Cong F M M E))))))))))))))))))))))))))) with (x := R).
---------------------------------------------------------------------------------------------------------------------------------intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> (euclidean__axioms.Cong F M M E0))))))))))))))))))) with (x := E).
----------------------------------------------------------------------------------------------------------------------------------intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
exact H74.

---------------------------------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------- exact H157.
---------------------------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------- exact H126.

--------------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D M M E) as H140.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (D) (M) (F) (M) (M) (E) (H138) H139).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C F M) as H141.
---------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (M) (F) (M) (C) H137).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C M F M) as H142.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M M F) /\ ((euclidean__axioms.Cong C M F M) /\ (euclidean__axioms.Cong M C M F))) as H142.
------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (M) (C) (F) (M) H141).
------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong C M M F) /\ ((euclidean__axioms.Cong C M F M) /\ (euclidean__axioms.Cong M C M F))) as H143.
------------------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong C M F M) /\ (euclidean__axioms.Cong M C M F)) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
exact H145.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M D M E) as H143.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong M D E M) /\ ((euclidean__axioms.Cong M D M E) /\ (euclidean__axioms.Cong D M E M))) as H143.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (M) (M) (E) H140).
------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M D E M) /\ ((euclidean__axioms.Cong M D M E) /\ (euclidean__axioms.Cong D M E M))) as H144.
-------------------------------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Cong M D M E) /\ (euclidean__axioms.Cong D M E M)) as H146.
--------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
exact H146.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS C M D) as H144.
------------------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> ((euclidean__axioms.Cong F M M R0) -> (euclidean__axioms.BetS C M D))))))))))))))))))))))))))) with (x := R).
--------------------------------------------------------------------------------------------------------------------------------------intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> ((euclidean__axioms.Cong F M M E0) -> ((euclidean__axioms.Cong D M M E0) -> ((euclidean__axioms.Cong M D M E0) -> (euclidean__axioms.BetS C M D)))))))))))))))))))))) with (x := E).
---------------------------------------------------------------------------------------------------------------------------------------intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
exact H149.

--------------------------------------------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------------------------------------------------------------------------- exact H3.
--------------------------------------------------------------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------------------------------------- exact H163.
--------------------------------------------------------------------------------------------------------------------------------------- exact H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------------------------- exact H166.
--------------------------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------------- exact H140.
--------------------------------------------------------------------------------------------------------------------------------------- exact H143.

-------------------------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------------------------------------------------------- exact H54.
-------------------------------------------------------------------------------------------------------------------------------------- exact H55.
-------------------------------------------------------------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------------------------- exact H127.
-------------------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F M E) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun R0: euclidean__axioms.Point => (euclidean__axioms.BetS D M R0) -> ((euclidean__axioms.Cong M R0 M D) -> ((euclidean__axioms.Cong M D M R0) -> ((euclidean__axioms.Cong D M M R0) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.BetS R0 M D) -> ((euclidean__axioms.Cong Q M M R0) -> ((euclidean__axioms.Cong Q M R0 M) -> ((euclidean__defs.Midpoint D M R0) -> ((euclidean__axioms.Cong D B R0 A) -> ((euclidean__axioms.Cong Q A R0 A) -> ((euclidean__axioms.Cong Q A A R0) -> ((euclidean__axioms.Cong D F R0 Q) -> ((euclidean__axioms.Cong F D Q R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.BetS Q A R0) -> ((euclidean__defs.Midpoint Q A R0) -> ((euclidean__axioms.Cong B D A R0) -> ((euclidean__axioms.Cong F D E R0) -> ((euclidean__axioms.BetS E A R0) -> ((euclidean__axioms.Cong A R0 B D) -> ((euclidean__axioms.Cong A R0 B F) -> ((euclidean__axioms.Cong A R0 A E) -> ((euclidean__axioms.Cong A R0 A C) -> ((euclidean__axioms.Cong F M M R0) -> (euclidean__axioms.BetS F M E))))))))))))))))))))))))))) with (x := R).
---------------------------------------------------------------------------------------------------------------------------------------intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
apply (@eq__ind__r euclidean__axioms.Point Q (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS C A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong C A A E0) -> ((euclidean__axioms.Cong C M E0 M) -> ((euclidean__axioms.Cong E0 M C M) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong E0 A A C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__defs.Midpoint E0 A C) -> ((euclidean__defs.Midpoint F M E0) -> ((euclidean__axioms.Cong F B E0 A) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong F D E0 C) -> ((euclidean__axioms.BetS E0 A C) -> ((euclidean__axioms.Cong B F A E0) -> ((euclidean__axioms.Cong A C A E0) -> ((euclidean__axioms.Cong A E0 A C) -> ((euclidean__axioms.Cong F M M E0) -> ((euclidean__axioms.Cong D M M E0) -> ((euclidean__axioms.Cong M D M E0) -> (euclidean__axioms.BetS F M E0)))))))))))))))))))))) with (x := E).
----------------------------------------------------------------------------------------------------------------------------------------intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
exact H51.

---------------------------------------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------------------------------------------------------------------- exact H106.
---------------------------------------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------------------------------- exact H164.
---------------------------------------------------------------------------------------------------------------------------------------- exact H163.
---------------------------------------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------------- exact H143.

--------------------------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------------------------- exact H37.
--------------------------------------------------------------------------------------------------------------------------------------- exact H38.
--------------------------------------------------------------------------------------------------------------------------------------- exact H53.
--------------------------------------------------------------------------------------------------------------------------------------- exact H54.
--------------------------------------------------------------------------------------------------------------------------------------- exact H55.
--------------------------------------------------------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------------------------------------------- exact H118.
--------------------------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D F E) as H146.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__sumofparts (C) (M) (D) (F) (M) (E) (H142) (H143) (H144) H145).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C D E F) as H147.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D C E F) /\ ((euclidean__axioms.Cong D C F E) /\ (euclidean__axioms.Cong C D E F))) as H147.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (D) (F) (E) H146).
----------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C E F) /\ ((euclidean__axioms.Cong D C F E) /\ (euclidean__axioms.Cong C D E F))) as H148.
------------------------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Cong D C F E) /\ (euclidean__axioms.Cong C D E F)) as H150.
------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
exact H151.
---------------------------------------------------------------------------------------------------------------------------------------- exact H147.
----------------------------------------------------------------------------------------------- exact H109.
Qed.
