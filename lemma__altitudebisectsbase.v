Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export logic.
Require Export proposition__04.
Definition lemma__altitudebisectsbase : forall A B M P, (euclidean__axioms.BetS A M B) -> ((euclidean__axioms.Cong A P B P) -> ((euclidean__defs.Per A M P) -> (euclidean__defs.Midpoint A M B))).
Proof.
intro A.
intro B.
intro M.
intro P.
intro H.
intro H0.
intro H1.
assert (exists C, (euclidean__axioms.BetS A M C) /\ ((euclidean__axioms.Cong A M C M) /\ ((euclidean__axioms.Cong A P C P) /\ (euclidean__axioms.neq M P)))) as H2 by exact H1.
destruct H2 as [C H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.BetS C M A) as H10.
- apply (@euclidean__axioms.axiom__betweennesssymmetry A M C H4).
- assert (* Cut *) (euclidean__axioms.Cong C M A M) as H11.
-- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C A M M H6).
-- assert (* Cut *) (euclidean__axioms.Cong C P A P) as H12.
--- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C A P P H8).
--- assert (* Cut *) (euclidean__defs.Per C M P) as H13.
---- exists A.
split.
----- exact H10.
----- split.
------ exact H11.
------ split.
------- exact H12.
------- exact H9.
---- assert (* Cut *) (euclidean__defs.Per P M A) as H14.
----- apply (@lemma__8__2.lemma__8__2 A M P H1).
----- assert (exists Q, (euclidean__axioms.BetS P M Q) /\ ((euclidean__axioms.Cong P M Q M) /\ ((euclidean__axioms.Cong P A Q A) /\ (euclidean__axioms.neq M A)))) as H15 by exact H14.
destruct H15 as [Q H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) (euclidean__axioms.Cong Q M P M) as H23.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric Q P M M H19).
------ assert (* Cut *) (euclidean__defs.Per P M C) as H24.
------- apply (@lemma__8__2.lemma__8__2 C M P H13).
------- assert (* Cut *) (euclidean__defs.Out M C B) as H25.
-------- exists A.
split.
--------- exact H.
--------- exact H4.
-------- assert (* Cut *) (euclidean__defs.Per P M B) as H26.
--------- apply (@lemma__8__3.lemma__8__3 P M C B H24 H25).
--------- assert (exists E, (euclidean__axioms.BetS P M E) /\ ((euclidean__axioms.Cong P M E M) /\ ((euclidean__axioms.Cong P B E B) /\ (euclidean__axioms.neq M B)))) as H27 by exact H26.
destruct H27 as [E H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
assert (* Cut *) (euclidean__axioms.Cong P A P B) as H35.
---------- assert (* Cut *) ((euclidean__axioms.Cong P A P B) /\ ((euclidean__axioms.Cong P A B P) /\ (euclidean__axioms.Cong A P P B))) as H35.
----------- apply (@lemma__congruenceflip.lemma__congruenceflip A P B P H0).
----------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H36.
---------- assert (* Cut *) (euclidean__axioms.Cong M Q P M) as H36.
----------- assert (* Cut *) ((euclidean__axioms.Cong M Q M P) /\ ((euclidean__axioms.Cong M Q P M) /\ (euclidean__axioms.Cong Q M M P))) as H36.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip Q M P M H23).
------------ destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H39.
----------- assert (* Cut *) (euclidean__axioms.Cong P M M Q) as H37.
------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric P M Q M H36).
------------ assert (* Cut *) (euclidean__axioms.Cong E M P M) as H38.
------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E P M M H31).
------------- assert (* Cut *) (euclidean__axioms.Cong E M M Q) as H39.
-------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive E M P M M Q H38 H37).
-------------- assert (* Cut *) (euclidean__axioms.Cong M E M Q) as H40.
--------------- assert (* Cut *) ((euclidean__axioms.Cong M E Q M) /\ ((euclidean__axioms.Cong M E M Q) /\ (euclidean__axioms.Cong E M Q M))) as H40.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip E M M Q H39).
---------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H43.
--------------- assert (* Cut *) (euclidean__axioms.Cong M Q M E) as H41.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M M E Q H40).
---------------- assert (* Cut *) (euclidean__axioms.neq P M) as H42.
----------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P E))) as H42.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal P M E H29).
------------------ destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H45.
----------------- assert (* Cut *) (Q = E) as H43.
------------------ apply (@lemma__extensionunique.lemma__extensionunique P M Q E H17 H29 H41).
------------------ assert (* Cut *) (euclidean__axioms.Cong P B Q B) as H44.
------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun Q0 => (euclidean__axioms.BetS P M Q0) -> ((euclidean__axioms.Cong P M Q0 M) -> ((euclidean__axioms.Cong P A Q0 A) -> ((euclidean__axioms.Cong Q0 M P M) -> ((euclidean__axioms.Cong M Q0 P M) -> ((euclidean__axioms.Cong P M M Q0) -> ((euclidean__axioms.Cong E M M Q0) -> ((euclidean__axioms.Cong M E M Q0) -> ((euclidean__axioms.Cong M Q0 M E) -> (euclidean__axioms.Cong P B Q0 B))))))))))) with (x := Q).
--------------------intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
exact H33.

-------------------- exact H43.
-------------------- exact H17.
-------------------- exact H19.
-------------------- exact H21.
-------------------- exact H23.
-------------------- exact H36.
-------------------- exact H37.
-------------------- exact H39.
-------------------- exact H40.
-------------------- exact H41.
------------------- assert (* Cut *) (euclidean__axioms.Cong A P P B) as H45.
-------------------- assert (* Cut *) ((euclidean__axioms.Cong A P B P) /\ ((euclidean__axioms.Cong A P P B) /\ (euclidean__axioms.Cong P A B P))) as H45.
--------------------- apply (@lemma__congruenceflip.lemma__congruenceflip P A P B H35).
--------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H48.
-------------------- assert (* Cut *) (euclidean__axioms.Cong A P Q B) as H46.
--------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A P P B Q B H45 H44).
--------------------- assert (* Cut *) (euclidean__axioms.Cong A Q A P) as H47.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong A Q A P) /\ (euclidean__axioms.Cong A P A Q)) as H47.
----------------------- apply (@lemma__doublereverse.lemma__doublereverse P A Q A H21).
----------------------- destruct H47 as [H48 H49].
exact H48.
---------------------- assert (* Cut *) (euclidean__axioms.Cong A Q Q B) as H48.
----------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A Q A P Q B H47 H46).
----------------------- assert (* Cut *) (euclidean__axioms.Cong A Q B Q) as H49.
------------------------ assert (* Cut *) ((euclidean__axioms.Cong Q A B Q) /\ ((euclidean__axioms.Cong Q A Q B) /\ (euclidean__axioms.Cong A Q B Q))) as H49.
------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A Q Q B H48).
------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
------------------------ assert (* Cut *) (euclidean__axioms.Cong P Q P Q) as H50.
------------------------- apply (@euclidean__axioms.cn__congruencereflexive P Q).
------------------------- assert (* Cut *) (A = A) as H51.
-------------------------- apply (@logic.eq__refl Point A).
-------------------------- assert (* Cut *) (B = B) as H52.
--------------------------- apply (@logic.eq__refl Point B).
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A M P) as H53.
---------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC A M P H1).
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col A P M)) as H54.
----------------------------- intro H54.
assert (* Cut *) (euclidean__axioms.Col A M P) as H55.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col P A M) /\ ((euclidean__axioms.Col P M A) /\ ((euclidean__axioms.Col M A P) /\ ((euclidean__axioms.Col A M P) /\ (euclidean__axioms.Col M P A))))) as H55.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A P M H54).
------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H62.
------------------------------ apply (@euclidean__tactics.Col__nCol__False A M P H53 H55).
----------------------------- assert (* Cut *) (~(A = P)) as H55.
------------------------------ intro H55.
assert (* Cut *) (euclidean__axioms.Col A P M) as H56.
------------------------------- left.
exact H55.
------------------------------- apply (@H54 H56).
------------------------------ assert (* Cut *) (euclidean__axioms.neq P A) as H56.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A P H55).
------------------------------- assert (* Cut *) (euclidean__defs.Out P A A) as H57.
-------------------------------- apply (@lemma__ray4.lemma__ray4 P A A).
---------------------------------right.
left.
exact H51.

--------------------------------- exact H56.
-------------------------------- assert (* Cut *) (~(P = B)) as H58.
--------------------------------- intro H58.
assert (* Cut *) (euclidean__axioms.Cong A P B B) as H59.
---------------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun P0 => (euclidean__axioms.Cong A P0 B P0) -> ((euclidean__defs.Per A M P0) -> ((euclidean__axioms.Cong A P0 C P0) -> ((euclidean__axioms.neq M P0) -> ((euclidean__axioms.Cong C P0 A P0) -> ((euclidean__defs.Per C M P0) -> ((euclidean__defs.Per P0 M A) -> ((euclidean__axioms.BetS P0 M Q) -> ((euclidean__axioms.Cong P0 M Q M) -> ((euclidean__axioms.Cong P0 A Q A) -> ((euclidean__axioms.Cong Q M P0 M) -> ((euclidean__defs.Per P0 M C) -> ((euclidean__defs.Per P0 M B) -> ((euclidean__axioms.BetS P0 M E) -> ((euclidean__axioms.Cong P0 M E M) -> ((euclidean__axioms.Cong P0 B E B) -> ((euclidean__axioms.Cong P0 A P0 B) -> ((euclidean__axioms.Cong M Q P0 M) -> ((euclidean__axioms.Cong P0 M M Q) -> ((euclidean__axioms.Cong E M P0 M) -> ((euclidean__axioms.neq P0 M) -> ((euclidean__axioms.Cong P0 B Q B) -> ((euclidean__axioms.Cong A P0 P0 B) -> ((euclidean__axioms.Cong A P0 Q B) -> ((euclidean__axioms.Cong A Q A P0) -> ((euclidean__axioms.Cong P0 Q P0 Q) -> ((euclidean__axioms.nCol A M P0) -> ((~(euclidean__axioms.Col A P0 M)) -> ((~(A = P0)) -> ((euclidean__axioms.neq P0 A) -> ((euclidean__defs.Out P0 A A) -> (euclidean__axioms.Cong A P0 B B))))))))))))))))))))))))))))))))) with (x := P).
-----------------------------------intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
apply (@eq__ind__r euclidean__axioms.Point E (fun Q0 => (euclidean__axioms.Cong B A Q0 A) -> ((euclidean__axioms.Cong B M Q0 M) -> ((euclidean__axioms.BetS B M Q0) -> ((euclidean__axioms.Cong Q0 M B M) -> ((euclidean__axioms.Cong B M M Q0) -> ((euclidean__axioms.Cong M Q0 B M) -> ((euclidean__axioms.Cong E M M Q0) -> ((euclidean__axioms.Cong M E M Q0) -> ((euclidean__axioms.Cong M Q0 M E) -> ((euclidean__axioms.Cong A Q0 A B) -> ((euclidean__axioms.Cong A B Q0 B) -> ((euclidean__axioms.Cong B B Q0 B) -> ((euclidean__axioms.Cong A Q0 Q0 B) -> ((euclidean__axioms.Cong A Q0 B Q0) -> ((euclidean__axioms.Cong B Q0 B Q0) -> (euclidean__axioms.Cong A B B B))))))))))))))))) with (x := Q).
------------------------------------intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
exact H81.

------------------------------------ exact H43.
------------------------------------ exact H68.
------------------------------------ exact H67.
------------------------------------ exact H66.
------------------------------------ exact H69.
------------------------------------ exact H77.
------------------------------------ exact H76.
------------------------------------ exact H39.
------------------------------------ exact H40.
------------------------------------ exact H41.
------------------------------------ exact H83.
------------------------------------ exact H82.
------------------------------------ exact H80.
------------------------------------ exact H48.
------------------------------------ exact H49.
------------------------------------ exact H84.

----------------------------------- exact H58.
----------------------------------- exact H0.
----------------------------------- exact H1.
----------------------------------- exact H8.
----------------------------------- exact H9.
----------------------------------- exact H12.
----------------------------------- exact H13.
----------------------------------- exact H14.
----------------------------------- exact H17.
----------------------------------- exact H19.
----------------------------------- exact H21.
----------------------------------- exact H23.
----------------------------------- exact H24.
----------------------------------- exact H26.
----------------------------------- exact H29.
----------------------------------- exact H31.
----------------------------------- exact H33.
----------------------------------- exact H35.
----------------------------------- exact H36.
----------------------------------- exact H37.
----------------------------------- exact H38.
----------------------------------- exact H42.
----------------------------------- exact H44.
----------------------------------- exact H45.
----------------------------------- exact H46.
----------------------------------- exact H47.
----------------------------------- exact H50.
----------------------------------- exact H53.
----------------------------------- exact H54.
----------------------------------- exact H55.
----------------------------------- exact H56.
----------------------------------- exact H57.
---------------------------------- assert (* Cut *) (~(euclidean__axioms.neq A P)) as H60.
----------------------------------- intro H60.
assert (* Cut *) (euclidean__axioms.neq B B) as H61.
------------------------------------ apply (@euclidean__axioms.axiom__nocollapse A P B B H60 H59).
------------------------------------ assert (* Cut *) (B = B) as H62.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun P0 => (euclidean__axioms.Cong A P0 B P0) -> ((euclidean__defs.Per A M P0) -> ((euclidean__axioms.Cong A P0 C P0) -> ((euclidean__axioms.neq M P0) -> ((euclidean__axioms.Cong C P0 A P0) -> ((euclidean__defs.Per C M P0) -> ((euclidean__defs.Per P0 M A) -> ((euclidean__axioms.BetS P0 M Q) -> ((euclidean__axioms.Cong P0 M Q M) -> ((euclidean__axioms.Cong P0 A Q A) -> ((euclidean__axioms.Cong Q M P0 M) -> ((euclidean__defs.Per P0 M C) -> ((euclidean__defs.Per P0 M B) -> ((euclidean__axioms.BetS P0 M E) -> ((euclidean__axioms.Cong P0 M E M) -> ((euclidean__axioms.Cong P0 B E B) -> ((euclidean__axioms.Cong P0 A P0 B) -> ((euclidean__axioms.Cong M Q P0 M) -> ((euclidean__axioms.Cong P0 M M Q) -> ((euclidean__axioms.Cong E M P0 M) -> ((euclidean__axioms.neq P0 M) -> ((euclidean__axioms.Cong P0 B Q B) -> ((euclidean__axioms.Cong A P0 P0 B) -> ((euclidean__axioms.Cong A P0 Q B) -> ((euclidean__axioms.Cong A Q A P0) -> ((euclidean__axioms.Cong P0 Q P0 Q) -> ((euclidean__axioms.nCol A M P0) -> ((~(euclidean__axioms.Col A P0 M)) -> ((~(A = P0)) -> ((euclidean__axioms.neq P0 A) -> ((euclidean__defs.Out P0 A A) -> ((euclidean__axioms.Cong A P0 B B) -> ((euclidean__axioms.neq A P0) -> (B = B))))))))))))))))))))))))))))))))))) with (x := P).
--------------------------------------intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
apply (@eq__ind__r euclidean__axioms.Point E (fun Q0 => (euclidean__axioms.Cong B A Q0 A) -> ((euclidean__axioms.Cong B M Q0 M) -> ((euclidean__axioms.BetS B M Q0) -> ((euclidean__axioms.Cong Q0 M B M) -> ((euclidean__axioms.Cong B M M Q0) -> ((euclidean__axioms.Cong M Q0 B M) -> ((euclidean__axioms.Cong E M M Q0) -> ((euclidean__axioms.Cong M E M Q0) -> ((euclidean__axioms.Cong M Q0 M E) -> ((euclidean__axioms.Cong A Q0 A B) -> ((euclidean__axioms.Cong A B Q0 B) -> ((euclidean__axioms.Cong B B Q0 B) -> ((euclidean__axioms.Cong A Q0 Q0 B) -> ((euclidean__axioms.Cong A Q0 B Q0) -> ((euclidean__axioms.Cong B Q0 B Q0) -> (B = B))))))))))))))))) with (x := Q).
---------------------------------------intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
exact H52.

--------------------------------------- exact H43.
--------------------------------------- exact H71.
--------------------------------------- exact H70.
--------------------------------------- exact H69.
--------------------------------------- exact H72.
--------------------------------------- exact H80.
--------------------------------------- exact H79.
--------------------------------------- exact H39.
--------------------------------------- exact H40.
--------------------------------------- exact H41.
--------------------------------------- exact H86.
--------------------------------------- exact H85.
--------------------------------------- exact H83.
--------------------------------------- exact H48.
--------------------------------------- exact H49.
--------------------------------------- exact H87.

-------------------------------------- exact H58.
-------------------------------------- exact H0.
-------------------------------------- exact H1.
-------------------------------------- exact H8.
-------------------------------------- exact H9.
-------------------------------------- exact H12.
-------------------------------------- exact H13.
-------------------------------------- exact H14.
-------------------------------------- exact H17.
-------------------------------------- exact H19.
-------------------------------------- exact H21.
-------------------------------------- exact H23.
-------------------------------------- exact H24.
-------------------------------------- exact H26.
-------------------------------------- exact H29.
-------------------------------------- exact H31.
-------------------------------------- exact H33.
-------------------------------------- exact H35.
-------------------------------------- exact H36.
-------------------------------------- exact H37.
-------------------------------------- exact H38.
-------------------------------------- exact H42.
-------------------------------------- exact H44.
-------------------------------------- exact H45.
-------------------------------------- exact H46.
-------------------------------------- exact H47.
-------------------------------------- exact H50.
-------------------------------------- exact H53.
-------------------------------------- exact H54.
-------------------------------------- exact H55.
-------------------------------------- exact H56.
-------------------------------------- exact H57.
-------------------------------------- exact H59.
-------------------------------------- exact H60.
------------------------------------- apply (@H54).
--------------------------------------apply (@euclidean__tactics.not__nCol__Col A P M).
---------------------------------------intro H63.
apply (@H61 H62).


----------------------------------- apply (@H54).
------------------------------------apply (@euclidean__tactics.not__nCol__Col A P M).
-------------------------------------intro H61.
apply (@H60 H55).


--------------------------------- assert (* Cut *) (euclidean__defs.Out P B B) as H59.
---------------------------------- apply (@lemma__ray4.lemma__ray4 P B B).
-----------------------------------right.
left.
exact H52.

----------------------------------- exact H58.
---------------------------------- assert (* Cut *) (euclidean__defs.Out P M Q) as H60.
----------------------------------- apply (@lemma__ray4.lemma__ray4 P M Q).
------------------------------------right.
right.
exact H17.

------------------------------------ exact H42.
----------------------------------- assert (* Cut *) (euclidean__defs.CongA A P M B P M) as H61.
------------------------------------ exists A.
exists Q.
exists B.
exists Q.
split.
------------------------------------- exact H57.
------------------------------------- split.
-------------------------------------- exact H60.
-------------------------------------- split.
--------------------------------------- exact H59.
--------------------------------------- split.
---------------------------------------- exact H60.
---------------------------------------- split.
----------------------------------------- exact H35.
----------------------------------------- split.
------------------------------------------ exact H50.
------------------------------------------ split.
------------------------------------------- exact H49.
------------------------------------------- apply (@euclidean__tactics.nCol__notCol A P M H54).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong P M P M) as H62.
------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive P M).
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A M B M) /\ ((euclidean__defs.CongA P A M P B M) /\ (euclidean__defs.CongA P M A P M B))) as H63.
-------------------------------------- apply (@proposition__04.proposition__04 P A M P B M H35 H62 H61).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A M M B) as H64.
--------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
assert (* Cut *) ((euclidean__axioms.Cong M A M B) /\ ((euclidean__axioms.Cong M A B M) /\ (euclidean__axioms.Cong A M M B))) as H68.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A M B M H64).
---------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H72.
--------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint A M B) as H65.
---------------------------------------- split.
----------------------------------------- exact H.
----------------------------------------- exact H64.
---------------------------------------- exact H65.
Qed.
