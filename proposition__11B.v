Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__notperp.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__planeseparation.
Require Export lemma__pointreflectionisometry.
Require Export lemma__rightangleNC.
Require Export lemma__rightreverse.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__10.
Require Export proposition__12.
Definition proposition__11B : forall A B C P, (euclidean__axioms.BetS A C B) -> ((euclidean__axioms.nCol A B P) -> (exists X, (euclidean__defs.Per A C X) /\ (euclidean__axioms.TS X A B P))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro H.
intro H0.
assert (* Cut *) (exists M, (euclidean__axioms.nCol A B M) /\ ((euclidean__defs.OS M P A B) /\ (~(euclidean__defs.Per A C M)))) as H1.
- apply (@lemma__notperp.lemma__notperp A B C P H H0).
- destruct H1 as [M H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.neq A B) as H7.
-- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H7.
--- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
--- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H11.
-- assert (* Cut *) (exists Q, euclidean__defs.Perp__at M Q A B Q) as H8.
--- apply (@proposition__12.proposition__12 A B M H3).
--- destruct H8 as [Q H9].
assert (exists E, (euclidean__axioms.Col M Q Q) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__defs.Per E Q M)))) as H10 by exact H9.
destruct H10 as [E H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
assert (* Cut *) (~(M = Q)) as H18.
---- intro H18.
assert (* Cut *) (euclidean__axioms.Col A B M) as H19.
----- apply (@eq__ind__r euclidean__axioms.Point Q (fun M0 => (euclidean__axioms.nCol A B M0) -> ((euclidean__defs.OS M0 P A B) -> ((~(euclidean__defs.Per A C M0)) -> ((euclidean__defs.Perp__at M0 Q A B Q) -> ((euclidean__axioms.Col M0 Q Q) -> ((euclidean__defs.Per E Q M0) -> (euclidean__axioms.Col A B M0)))))))) with (x := M).
------intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
exact H14.

------ exact H18.
------ exact H3.
------ exact H5.
------ exact H6.
------ exact H9.
------ exact H12.
------ exact H17.
----- apply (@euclidean__tactics.Col__nCol__False A B M H3 H19).
---- assert (* Cut *) (euclidean__axioms.neq Q M) as H19.
----- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M Q H18).
----- assert (* Cut *) (euclidean__axioms.Col A B C) as H20.
------ right.
right.
right.
right.
right.
exact H.
------ assert (* Cut *) (euclidean__axioms.Col B A E) as H21.
------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H21.
-------- apply (@lemma__collinearorder.lemma__collinearorder A B E H16).
-------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H22.
------- assert (* Cut *) (euclidean__axioms.Col B A C) as H22.
-------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H22.
--------- apply (@lemma__collinearorder.lemma__collinearorder A B C H20).
--------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
-------- assert (* Cut *) (euclidean__axioms.neq B A) as H23.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H7).
--------- assert (* Cut *) (~(C = Q)) as H24.
---------- intro H24.
assert (* Cut *) (euclidean__defs.Per E C M) as H25.
----------- apply (@eq__ind__r euclidean__axioms.Point Q (fun C0 => (euclidean__axioms.BetS A C0 B) -> ((~(euclidean__defs.Per A C0 M)) -> ((euclidean__axioms.Col A B C0) -> ((euclidean__axioms.Col B A C0) -> (euclidean__defs.Per E C0 M)))))) with (x := C).
------------intro H25.
intro H26.
intro H27.
intro H28.
exact H17.

------------ exact H24.
------------ exact H.
------------ exact H6.
------------ exact H20.
------------ exact H22.
----------- assert (* Cut *) (euclidean__axioms.Col A E C) as H26.
------------ apply (@euclidean__tactics.not__nCol__Col A E C).
-------------intro H26.
apply (@euclidean__tactics.Col__nCol__False A E C H26).
--------------apply (@lemma__collinear4.lemma__collinear4 B A E C H21 H22 H23).


------------ assert (* Cut *) (euclidean__axioms.Col E C A) as H27.
------------- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H27.
-------------- apply (@lemma__collinearorder.lemma__collinearorder A E C H26).
-------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H30.
------------- assert (* Cut *) (euclidean__axioms.neq A C) as H28.
-------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H28.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
--------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
-------------- assert (* Cut *) (euclidean__defs.Per A C M) as H29.
--------------- apply (@lemma__collinearright.lemma__collinearright E C A M H25 H27 H28).
--------------- apply (@H6 H29).
---------- assert (* Cut *) (euclidean__axioms.Col C Q E) as H25.
----------- apply (@euclidean__tactics.not__nCol__Col C Q E).
------------intro H25.
apply (@euclidean__tactics.Col__nCol__False C Q E H25).
-------------apply (@lemma__collinear5.lemma__collinear5 A B C Q E H7 H20 H14 H16).


----------- assert (* Cut *) (euclidean__axioms.Col E Q C) as H26.
------------ assert (* Cut *) ((euclidean__axioms.Col Q C E) /\ ((euclidean__axioms.Col Q E C) /\ ((euclidean__axioms.Col E C Q) /\ ((euclidean__axioms.Col C E Q) /\ (euclidean__axioms.Col E Q C))))) as H26.
------------- apply (@lemma__collinearorder.lemma__collinearorder C Q E H25).
------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H34.
------------ assert (* Cut *) (euclidean__defs.Per C Q M) as H27.
------------- apply (@lemma__collinearright.lemma__collinearright E Q C M H17 H26 H24).
------------- assert (* Cut *) (euclidean__axioms.neq Q C) as H28.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C Q H24).
-------------- assert (* Cut *) (exists G, (euclidean__axioms.BetS Q G C) /\ (euclidean__axioms.Cong G Q G C)) as H29.
--------------- apply (@proposition__10.proposition__10 Q C H28).
--------------- destruct H29 as [G H30].
destruct H30 as [H31 H32].
assert (* Cut *) (~(M = G)) as H33.
---------------- intro H33.
assert (* Cut *) (euclidean__axioms.BetS Q M C) as H34.
----------------- apply (@eq__ind__r euclidean__axioms.Point G (fun M0 => (euclidean__axioms.nCol A B M0) -> ((euclidean__defs.OS M0 P A B) -> ((~(euclidean__defs.Per A C M0)) -> ((euclidean__defs.Perp__at M0 Q A B Q) -> ((euclidean__axioms.Col M0 Q Q) -> ((euclidean__defs.Per E Q M0) -> ((~(M0 = Q)) -> ((euclidean__axioms.neq Q M0) -> ((euclidean__defs.Per C Q M0) -> (euclidean__axioms.BetS Q M0 C))))))))))) with (x := M).
------------------intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
exact H31.

------------------ exact H33.
------------------ exact H3.
------------------ exact H5.
------------------ exact H6.
------------------ exact H9.
------------------ exact H12.
------------------ exact H17.
------------------ exact H18.
------------------ exact H19.
------------------ exact H27.
----------------- assert (* Cut *) (euclidean__axioms.Col Q M C) as H35.
------------------ right.
right.
right.
right.
left.
exact H34.
------------------ assert (* Cut *) (euclidean__axioms.Col B Q C) as H36.
------------------- apply (@euclidean__tactics.not__nCol__Col B Q C).
--------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False B Q C H36).
---------------------apply (@lemma__collinear4.lemma__collinear4 A B Q C H14 H20 H7).


------------------- assert (* Cut *) (euclidean__axioms.Col Q C M) as H37.
-------------------- assert (* Cut *) ((euclidean__axioms.Col M Q C) /\ ((euclidean__axioms.Col M C Q) /\ ((euclidean__axioms.Col C Q M) /\ ((euclidean__axioms.Col Q C M) /\ (euclidean__axioms.Col C M Q))))) as H37.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder Q M C H35).
--------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H44.
-------------------- assert (* Cut *) (euclidean__axioms.Col Q C B) as H38.
--------------------- assert (* Cut *) ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col Q C B) /\ ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col B C Q) /\ (euclidean__axioms.Col C Q B))))) as H38.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B Q C H36).
---------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H41.
--------------------- assert (* Cut *) (euclidean__axioms.neq Q C) as H39.
---------------------- assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq Q M) /\ (euclidean__axioms.neq Q C))) as H39.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q M C H34).
----------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H43.
---------------------- assert (* Cut *) (euclidean__axioms.Col C M B) as H40.
----------------------- apply (@euclidean__tactics.not__nCol__Col C M B).
------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False C M B H40).
-------------------------apply (@lemma__collinear4.lemma__collinear4 Q C M B H37 H38 H39).


----------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H41.
------------------------ assert (* Cut *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col C B M) /\ (euclidean__axioms.Col B M C))))) as H41.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder C M B H40).
------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H48.
------------------------ assert (* Cut *) (euclidean__axioms.Col C B A) as H42.
------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H42.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H22).
-------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H47.
------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H43.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H43.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
--------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H44.
-------------------------- assert (* Cut *) (euclidean__axioms.Col B M A) as H44.
--------------------------- apply (@euclidean__tactics.not__nCol__Col B M A).
----------------------------intro H44.
apply (@euclidean__tactics.Col__nCol__False B M A H44).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 C B M A H41 H42 H43).


--------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H45.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H45.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M A H44).
----------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H50.
---------------------------- apply (@euclidean__tactics.Col__nCol__False A B M H3 H45).
---------------- assert (* Cut *) (exists H34, (euclidean__axioms.BetS M G H34) /\ (euclidean__axioms.Cong G H34 M G)) as H34.
----------------- apply (@lemma__extension.lemma__extension M G M G H33 H33).
----------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
assert (* Cut *) (euclidean__axioms.Cong M G G H35) as H39.
------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M G H35 G H38).
------------------ assert (* Cut *) (euclidean__defs.Midpoint M G H35) as H40.
------------------- split.
-------------------- exact H37.
-------------------- exact H39.
------------------- assert (* Cut *) (euclidean__axioms.Cong Q G G C) as H41.
-------------------- assert (* Cut *) ((euclidean__axioms.Cong Q G C G) /\ ((euclidean__axioms.Cong Q G G C) /\ (euclidean__axioms.Cong G Q C G))) as H41.
--------------------- apply (@lemma__congruenceflip.lemma__congruenceflip G Q G C H32).
--------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H44.
-------------------- assert (* Cut *) (euclidean__defs.Midpoint Q G C) as H42.
--------------------- split.
---------------------- exact H31.
---------------------- exact H41.
--------------------- assert (* Cut *) (euclidean__axioms.Col Q G C) as H43.
---------------------- right.
right.
right.
right.
left.
exact H31.
---------------------- assert (* Cut *) (euclidean__axioms.Col C Q G) as H44.
----------------------- assert (* Cut *) ((euclidean__axioms.Col G Q C) /\ ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col C Q G) /\ ((euclidean__axioms.Col Q C G) /\ (euclidean__axioms.Col C G Q))))) as H44.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder Q G C H43).
------------------------ destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
----------------------- assert (* Cut *) (euclidean__axioms.neq Q G) as H45.
------------------------ assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q C))) as H45.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G C H31).
------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H48.
------------------------ assert (* Cut *) (euclidean__axioms.neq G Q) as H46.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric Q G H45).
------------------------- assert (* Cut *) (euclidean__defs.Per G Q M) as H47.
-------------------------- apply (@lemma__collinearright.lemma__collinearright C Q G M H27 H44 H46).
-------------------------- assert (* Cut *) (exists J, (euclidean__axioms.BetS M Q J) /\ (euclidean__axioms.Cong Q J M Q)) as H48.
--------------------------- apply (@lemma__extension.lemma__extension M Q M Q H18 H18).
--------------------------- destruct H48 as [J H49].
destruct H49 as [H50 H51].
assert (* Cut *) (euclidean__axioms.Cong M Q Q J) as H52.
---------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M Q J Q H51).
---------------------------- assert (* Cut *) (euclidean__defs.Per M Q G) as H53.
----------------------------- apply (@lemma__8__2.lemma__8__2 G Q M H47).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong M G J G) as H54.
------------------------------ apply (@lemma__rightreverse.lemma__rightreverse M Q G J H53 H50 H52).
------------------------------ assert (* Cut *) (euclidean__axioms.BetS J Q M) as H55.
------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry M Q J H50).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong J Q M Q) as H56.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Cong J Q Q M) /\ ((euclidean__axioms.Cong J Q M Q) /\ (euclidean__axioms.Cong Q J Q M))) as H56.
--------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip Q J M Q H51).
--------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H59.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong J G M G) as H57.
--------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric J M G G H54).
--------------------------------- assert (* Cut *) (euclidean__defs.Per J Q G) as H58.
---------------------------------- exists M.
split.
----------------------------------- exact H55.
----------------------------------- split.
------------------------------------ exact H56.
------------------------------------ split.
------------------------------------- exact H57.
------------------------------------- exact H45.
---------------------------------- assert (* Cut *) (~(J = G)) as H59.
----------------------------------- intro H59.
assert (* Cut *) (euclidean__axioms.Col J Q G) as H60.
------------------------------------ right.
left.
exact H59.
------------------------------------ assert (* Cut *) (euclidean__axioms.nCol J Q G) as H61.
------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC J Q G H58).
------------------------------------- apply (@euclidean__tactics.Col__nCol__False J Q G H61 H60).
----------------------------------- assert (* Cut *) (exists K, (euclidean__axioms.BetS J G K) /\ (euclidean__axioms.Cong G K J G)) as H60.
------------------------------------ apply (@lemma__extension.lemma__extension J G J G H59 H59).
------------------------------------ destruct H60 as [K H61].
destruct H61 as [H62 H63].
assert (* Cut *) (euclidean__axioms.Cong J G G K) as H64.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric J G K G H63).
------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint J G K) as H65.
-------------------------------------- split.
--------------------------------------- exact H62.
--------------------------------------- exact H64.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M Q H35 C) as H66.
--------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry M G H35 Q C H40 H42 H18).
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq J Q) as H67.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q M) /\ ((euclidean__axioms.neq J Q) /\ (euclidean__axioms.neq J M))) as H67.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal J Q M H55).
----------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H70.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q J) as H68.
----------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric J Q H67).
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq M J) as H69.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq Q J) /\ ((euclidean__axioms.neq M Q) /\ (euclidean__axioms.neq M J))) as H69.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal M Q J H50).
------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H73.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong Q J C K) as H70.
------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry Q G C J K H42 H65 H68).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M J H35 K) as H71.
-------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry M G H35 J K H40 H65 H69).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H35 C K) as H72.
--------------------------------------------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved M Q J H35 C K H66 H71 H70 H50).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H35 G G M) as H73.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H35 G G M) /\ ((euclidean__axioms.Cong H35 G M G) /\ (euclidean__axioms.Cong G H35 G M))) as H73.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip G H35 M G H38).
----------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H74.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G M J G) as H74.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G M G J) /\ ((euclidean__axioms.Cong G M J G) /\ (euclidean__axioms.Cong M G G J))) as H74.
------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip M G J G H54).
------------------------------------------------ destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H77.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H35 G J G) as H75.
------------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive H35 G G M J G H73 H74).
------------------------------------------------ assert (euclidean__axioms.Cong J G G K) as H76 by exact H64.
assert (* Cut *) (euclidean__axioms.Cong H35 G G K) as H77.
------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive H35 G J G G K H75 H76).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H35 G K G) as H78.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G H35 K G) /\ ((euclidean__axioms.Cong G H35 G K) /\ (euclidean__axioms.Cong H35 G K G))) as H78.
--------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip H35 G G K H77).
--------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H82.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H79.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq Q G) /\ (euclidean__axioms.neq Q C))) as H79.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q G C H31).
---------------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H80.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H35 C M Q) as H80.
---------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric H35 M Q C H66).
---------------------------------------------------- assert (euclidean__axioms.Cong M Q Q J) as H81 by exact H52.
assert (* Cut *) (euclidean__axioms.Cong H35 C Q J) as H82.
----------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive H35 C M Q Q J H80 H81).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H35 C C K) as H83.
------------------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive H35 C Q J C K H82 H70).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong H35 C K C) as H84.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C H35 K C) /\ ((euclidean__axioms.Cong C H35 C K) /\ (euclidean__axioms.Cong H35 C K C))) as H84.
-------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip H35 C C K H83).
-------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H88.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H85.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C K) /\ ((euclidean__axioms.neq H35 C) /\ (euclidean__axioms.neq H35 K))) as H85.
--------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H35 C K H72).
--------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H79.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H86.
--------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G C H85).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per H35 C G) as H87.
---------------------------------------------------------- exists K.
split.
----------------------------------------------------------- exact H72.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H84.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H78.
------------------------------------------------------------- exact H86.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per G C H35) as H88.
----------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 H35 C G H87).
----------------------------------------------------------- assert (* Cut *) (A = A) as H89.
------------------------------------------------------------ apply (@logic.eq__refl Point A).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B A) as H90.
------------------------------------------------------------- right.
left.
exact H89.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C A) as H91.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col Q C A).
---------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False Q C A H91).
----------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 A B Q C A H7 H14 H20 H90).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q C G) as H92.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q C G) /\ ((euclidean__axioms.Col Q G C) /\ ((euclidean__axioms.Col G C Q) /\ ((euclidean__axioms.Col C G Q) /\ (euclidean__axioms.Col G Q C))))) as H92.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C Q G H44).
---------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H93.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A G) as H93.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C A G).
-----------------------------------------------------------------intro H93.
apply (@euclidean__tactics.Col__nCol__False C A G H93).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 Q C A G H91 H92 H28).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C A) as H94.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col G C A) /\ ((euclidean__axioms.Col C G A) /\ (euclidean__axioms.Col G A C))))) as H94.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C A G H93).
------------------------------------------------------------------ destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H99.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A C) as H95.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H95.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
------------------------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H98.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per A C H35) as H96.
------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright G C A H35 H88 H94 H95).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H97.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H97.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H22).
--------------------------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H105.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C A) as H98.
--------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A C H95).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G B) as H99.
---------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A G B).
-----------------------------------------------------------------------intro H99.
apply (@euclidean__tactics.Col__nCol__False A G B H99).
------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C A G B H93 H97 H98).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H100.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H100.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A G B H99).
------------------------------------------------------------------------ destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
exact H107.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS P M A B) as H101.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.OS P M A B) /\ ((euclidean__defs.OS M P B A) /\ (euclidean__defs.OS P M B A))) as H101.
------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B M P H5).
------------------------------------------------------------------------- destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H102.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS M A B H35) as H102.
------------------------------------------------------------------------- exists G.
split.
-------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------- exact H3.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS P A B H35) as H103.
-------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation A B P M H35 H101 H102).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS H35 A B P) as H104.
--------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric A B P H35 H103).
--------------------------------------------------------------------------- exists H35.
split.
---------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------- exact H104.
Qed.
