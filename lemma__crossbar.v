Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__crossbar : forall A B C E U V, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.BetS A E C) -> ((euclidean__defs.Out B A U) -> ((euclidean__defs.Out B C V) -> (exists X, (euclidean__defs.Out B E X) /\ (euclidean__axioms.BetS U X V))))).
Proof.
intro A.
intro B.
intro C.
intro E.
intro U.
intro V.
intro H.
intro H0.
intro H1.
intro H2.
assert (euclidean__axioms.nCol A B C) as H3 by exact H.
assert (* Cut *) (~(B = E)) as H4.
- intro H4.
assert (* Cut *) (~(euclidean__axioms.BetS A B C)) as H5.
-- intro H5.
assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
--- right.
right.
right.
right.
left.
exact H5.
--- apply (@euclidean__tactics.Col__nCol__False A B C H3 H6).
-- assert (* Cut *) (euclidean__axioms.BetS A B C) as H6.
--- apply (@eq__ind__r euclidean__axioms.Point E (fun B0 => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Out B0 A U) -> ((euclidean__defs.Out B0 C V) -> ((euclidean__axioms.nCol A B0 C) -> ((~(euclidean__axioms.BetS A B0 C)) -> (euclidean__axioms.BetS A B0 C))))))) with (x := B).
----intro H6.
intro H7.
intro H8.
intro H9.
intro H10.
exact H0.

---- exact H4.
---- exact H.
---- exact H1.
---- exact H2.
---- exact H3.
---- exact H5.
--- apply (@H5 H6).
- assert (* Cut *) (~(B = A)) as H5.
-- intro H5.
assert (* Cut *) (A = B) as H6.
--- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric A B H5).
--- assert (* Cut *) (euclidean__axioms.Col A B C) as H7.
---- left.
exact H6.
---- apply (@euclidean__tactics.Col__nCol__False A B C H3 H7).
-- assert (* Cut *) (~(B = C)) as H6.
--- intro H6.
assert (* Cut *) (euclidean__axioms.Col A B C) as H7.
---- right.
right.
left.
exact H6.
---- apply (@euclidean__tactics.Col__nCol__False A B C H3 H7).
--- assert (* Cut *) (euclidean__axioms.neq B U) as H7.
---- apply (@lemma__raystrict.lemma__raystrict B A U H1).
---- assert (* Cut *) (euclidean__axioms.neq B V) as H8.
----- apply (@lemma__raystrict.lemma__raystrict B C V H2).
----- assert (* Cut *) (exists P, (euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P B U)) as H9.
------ apply (@lemma__extension.lemma__extension B A B U H5 H7).
------ destruct H9 as [P H10].
destruct H10 as [H11 H12].
assert (* Cut *) (exists Q, (euclidean__axioms.BetS B C Q) /\ (euclidean__axioms.Cong C Q B V)) as H13.
------- apply (@lemma__extension.lemma__extension B C B V H6 H8).
------- destruct H13 as [Q H14].
destruct H14 as [H15 H16].
assert (* Cut *) (~(euclidean__axioms.Col B Q A)) as H17.
-------- intro H17.
assert (* Cut *) (euclidean__axioms.Col Q B A) as H18.
--------- assert (* Cut *) ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B))))) as H18.
---------- apply (@lemma__collinearorder.lemma__collinearorder B Q A H17).
---------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
--------- assert (* Cut *) (euclidean__axioms.Col B C Q) as H19.
---------- right.
right.
right.
right.
left.
exact H15.
---------- assert (* Cut *) (euclidean__axioms.Col Q B C) as H20.
----------- assert (* Cut *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B))))) as H20.
------------ apply (@lemma__collinearorder.lemma__collinearorder B C Q H19).
------------ destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
----------- assert (* Cut *) (euclidean__axioms.neq B Q) as H21.
------------ assert (* Cut *) ((euclidean__axioms.neq C Q) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B Q))) as H21.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal B C Q H15).
------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H25.
------------ assert (* Cut *) (euclidean__axioms.neq Q B) as H22.
------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B Q H21).
------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H23.
-------------- apply (@euclidean__tactics.not__nCol__Col B A C).
---------------intro H23.
apply (@euclidean__tactics.Col__nCol__False B A C H23).
----------------apply (@lemma__collinear4.lemma__collinear4 Q B A C H18 H20 H22).


-------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H24.
--------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H24.
---------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H23).
---------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
--------------- apply (@euclidean__tactics.Col__nCol__False A B C H3 H24).
-------- assert (* Cut *) (exists F, (euclidean__axioms.BetS A F Q) /\ (euclidean__axioms.BetS B E F)) as H18.
--------- apply (@euclidean__axioms.postulate__Pasch__outer A B C E Q H0 H15).
----------apply (@euclidean__tactics.nCol__notCol B Q A H17).

--------- destruct H18 as [F H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__axioms.BetS Q F A) as H22.
---------- apply (@euclidean__axioms.axiom__betweennesssymmetry A F Q H20).
---------- assert (* Cut *) (~(euclidean__axioms.Col B P Q)) as H23.
----------- intro H23.
assert (* Cut *) (euclidean__axioms.Col P B Q) as H24.
------------ assert (* Cut *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))))) as H24.
------------- apply (@lemma__collinearorder.lemma__collinearorder B P Q H23).
------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
------------ assert (* Cut *) (euclidean__axioms.Col B A P) as H25.
------------- right.
right.
right.
right.
left.
exact H11.
------------- assert (* Cut *) (euclidean__axioms.Col P B A) as H26.
-------------- assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H26.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B A P H25).
--------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H31.
-------------- assert (* Cut *) (euclidean__axioms.neq B P) as H27.
--------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P))) as H27.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal B A P H11).
---------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H31.
--------------- assert (* Cut *) (euclidean__axioms.neq P B) as H28.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B P H27).
---------------- assert (* Cut *) (euclidean__axioms.Col B Q A) as H29.
----------------- apply (@euclidean__tactics.not__nCol__Col B Q A).
------------------intro H29.
apply (@H17).
-------------------apply (@lemma__collinear4.lemma__collinear4 P B Q A H24 H26 H28).


----------------- apply (@H17 H29).
----------- assert (* Cut *) (exists W, (euclidean__axioms.BetS Q W P) /\ (euclidean__axioms.BetS B F W)) as H24.
------------ apply (@euclidean__axioms.postulate__Pasch__outer Q B A F P H22 H11).
-------------apply (@euclidean__tactics.nCol__notCol B P Q H23).

------------ destruct H24 as [W H25].
destruct H25 as [H26 H27].
assert (* Cut *) (euclidean__axioms.BetS B E W) as H28.
------------- apply (@lemma__3__6b.lemma__3__6b B E F W H21 H27).
------------- assert (exists J, (euclidean__axioms.BetS J B U) /\ (euclidean__axioms.BetS J B A)) as H29 by exact H1.
destruct H29 as [J H30].
destruct H30 as [H31 H32].
assert (* Cut *) (euclidean__axioms.Cong A P P A) as H33.
-------------- apply (@euclidean__axioms.cn__equalityreverse A P).
-------------- assert (* Cut *) (euclidean__axioms.Cong B U A P) as H34.
--------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B A P U H12).
--------------- assert (* Cut *) (euclidean__axioms.Cong B U P A) as H35.
---------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B U A P P A H34 H33).
---------------- assert (* Cut *) (euclidean__axioms.Cong P A B U) as H36.
----------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric P B U A H35).
----------------- assert (* Cut *) (euclidean__axioms.BetS P A B) as H37.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry B A P H11).
------------------ assert (* Cut *) (euclidean__defs.Lt B U P B) as H38.
------------------- exists A.
split.
-------------------- exact H37.
-------------------- exact H36.
------------------- assert (* Cut *) (euclidean__axioms.Cong P B B P) as H39.
-------------------- apply (@euclidean__axioms.cn__equalityreverse P B).
-------------------- assert (* Cut *) (euclidean__defs.Lt B U B P) as H40.
--------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence B U P B B P H38 H39).
--------------------- assert (exists S, (euclidean__axioms.BetS B S P) /\ (euclidean__axioms.Cong B S B U)) as H41 by exact H40.
destruct H41 as [S H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.BetS J B P) as H45.
---------------------- apply (@lemma__3__7b.lemma__3__7b J B A P H32 H11).
---------------------- assert (* Cut *) (euclidean__axioms.BetS J B S) as H46.
----------------------- apply (@euclidean__axioms.axiom__innertransitivity J B S P H45 H43).
----------------------- assert (* Cut *) (S = U) as H47.
------------------------ apply (@lemma__extensionunique.lemma__extensionunique J B S U H46 H31 H44).
------------------------ assert (* Cut *) (euclidean__axioms.BetS B U P) as H48.
------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun S0 => (euclidean__axioms.BetS B S0 P) -> ((euclidean__axioms.Cong B S0 B U) -> ((euclidean__axioms.BetS J B S0) -> (euclidean__axioms.BetS B U P))))) with (x := S).
--------------------------intro H48.
intro H49.
intro H50.
exact H48.

-------------------------- exact H47.
-------------------------- exact H43.
-------------------------- exact H44.
-------------------------- exact H46.
------------------------- assert (exists K, (euclidean__axioms.BetS K B V) /\ (euclidean__axioms.BetS K B C)) as H49 by exact H2.
destruct H49 as [K H50].
destruct H50 as [H51 H52].
assert (* Cut *) (euclidean__axioms.Cong B V C Q) as H53.
-------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B C Q V H16).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong C Q Q C) as H54.
--------------------------- apply (@euclidean__axioms.cn__equalityreverse C Q).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong B V Q C) as H55.
---------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B V C Q Q C H53 H54).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong Q C B V) as H56.
----------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric Q B V C H55).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS Q C B) as H57.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry B C Q H15).
------------------------------ assert (* Cut *) (euclidean__defs.Lt B V Q B) as H58.
------------------------------- exists C.
split.
-------------------------------- exact H57.
-------------------------------- exact H56.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q B B Q) as H59.
-------------------------------- apply (@euclidean__axioms.cn__equalityreverse Q B).
-------------------------------- assert (* Cut *) (euclidean__defs.Lt B V B Q) as H60.
--------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence B V Q B B Q H58 H59).
--------------------------------- assert (exists R, (euclidean__axioms.BetS B R Q) /\ (euclidean__axioms.Cong B R B V)) as H61 by exact H60.
destruct H61 as [R H62].
destruct H62 as [H63 H64].
assert (* Cut *) (euclidean__axioms.BetS K B Q) as H65.
---------------------------------- apply (@lemma__3__7b.lemma__3__7b K B C Q H52 H15).
---------------------------------- assert (* Cut *) (euclidean__axioms.BetS K B R) as H66.
----------------------------------- apply (@euclidean__axioms.axiom__innertransitivity K B R Q H65 H63).
----------------------------------- assert (* Cut *) (R = V) as H67.
------------------------------------ apply (@lemma__extensionunique.lemma__extensionunique K B R V H66 H51 H64).
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B V Q) as H68.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point V (fun R0 => (euclidean__axioms.BetS B R0 Q) -> ((euclidean__axioms.Cong B R0 B V) -> ((euclidean__axioms.BetS K B R0) -> (euclidean__axioms.BetS B V Q))))) with (x := R).
--------------------------------------intro H68.
intro H69.
intro H70.
apply (@eq__ind__r euclidean__axioms.Point U (fun S0 => (euclidean__axioms.BetS B S0 P) -> ((euclidean__axioms.Cong B S0 B U) -> ((euclidean__axioms.BetS J B S0) -> (euclidean__axioms.BetS B V Q))))) with (x := S).
---------------------------------------intro H71.
intro H72.
intro H73.
exact H68.

--------------------------------------- exact H47.
--------------------------------------- exact H43.
--------------------------------------- exact H44.
--------------------------------------- exact H46.

-------------------------------------- exact H67.
-------------------------------------- exact H63.
-------------------------------------- exact H64.
-------------------------------------- exact H66.
------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col Q P B)) as H69.
-------------------------------------- intro H69.
assert (* Cut *) (euclidean__axioms.Col B P Q) as H70.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q B P) /\ (euclidean__axioms.Col B P Q))))) as H70.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q P B H69).
---------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
--------------------------------------- apply (@H17).
----------------------------------------apply (@euclidean__tactics.not__nCol__Col B Q A).
-----------------------------------------intro H71.
apply (@H23 H70).


-------------------------------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS Q M U) /\ (euclidean__axioms.BetS B M W)) as H70.
--------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner Q B P W U H26 H48).
----------------------------------------apply (@euclidean__tactics.nCol__notCol Q P B H69).

--------------------------------------- destruct H70 as [M H71].
destruct H71 as [H72 H73].
assert (* Cut *) (euclidean__axioms.BetS U M Q) as H74.
---------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry Q M U H72).
---------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col U Q B)) as H75.
----------------------------------------- intro H75.
assert (* Cut *) (euclidean__axioms.Col B U P) as H76.
------------------------------------------ right.
right.
right.
right.
left.
exact H48.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B U Q) as H77.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q U B) /\ ((euclidean__axioms.Col Q B U) /\ ((euclidean__axioms.Col B U Q) /\ ((euclidean__axioms.Col U B Q) /\ (euclidean__axioms.Col B Q U))))) as H77.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder U Q B H75).
-------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H82.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H78.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq U M) /\ (euclidean__axioms.neq U Q))) as H78.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal U M Q H74).
--------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H7.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col U B P) as H79.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col U B P) /\ ((euclidean__axioms.Col U P B) /\ ((euclidean__axioms.Col P B U) /\ ((euclidean__axioms.Col B P U) /\ (euclidean__axioms.Col P U B))))) as H79.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B U P H76).
---------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H80.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col U B Q) as H80.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col U B Q) /\ ((euclidean__axioms.Col U Q B) /\ ((euclidean__axioms.Col Q B U) /\ ((euclidean__axioms.Col B Q U) /\ (euclidean__axioms.Col Q U B))))) as H80.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B U Q H77).
----------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H81.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq U B) as H81.
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B U H78).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B P Q) as H82.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col B P Q).
-------------------------------------------------intro H82.
apply (@H23).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 U B P Q H79 H80 H81).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col Q P B) as H83.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))))) as H83.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B P Q H82).
-------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H91.
------------------------------------------------- apply (@H17).
--------------------------------------------------apply (@euclidean__tactics.not__nCol__Col B Q A).
---------------------------------------------------intro H84.
apply (@H23 H82).


----------------------------------------- assert (* Cut *) (exists H76, (euclidean__axioms.BetS U H76 V) /\ (euclidean__axioms.BetS B H76 M)) as H76.
------------------------------------------ apply (@euclidean__axioms.postulate__Pasch__inner U B Q M V H74 H68).
-------------------------------------------apply (@euclidean__tactics.nCol__notCol U Q B H75).

------------------------------------------ destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
assert (* Cut *) (~(E = B)) as H81.
------------------------------------------- intro H81.
assert (* Cut *) (B = E) as H82.
-------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric B E H81).
-------------------------------------------- apply (@H4 H82).
------------------------------------------- assert (* Cut *) (exists N, (euclidean__axioms.BetS E B N) /\ (euclidean__axioms.Cong B N B E)) as H82.
-------------------------------------------- apply (@lemma__extension.lemma__extension E B B E H81 H4).
-------------------------------------------- destruct H82 as [N H83].
destruct H83 as [H84 H85].
assert (* Cut *) (euclidean__axioms.BetS N B E) as H86.
--------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E B N H84).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B H77 W) as H87.
---------------------------------------------- apply (@lemma__3__6b.lemma__3__6b B H77 M W H80 H73).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS N B W) as H88.
----------------------------------------------- apply (@lemma__3__7b.lemma__3__7b N B E W H86 H28).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS N B H77) as H89.
------------------------------------------------ apply (@euclidean__axioms.axiom__innertransitivity N B H77 W H88 H87).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B E H77) as H90.
------------------------------------------------- exists N.
split.
-------------------------------------------------- exact H89.
-------------------------------------------------- exact H86.
------------------------------------------------- exists H77.
split.
-------------------------------------------------- exact H90.
-------------------------------------------------- exact H79.
Qed.
