Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__7.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export lemma__sameside2.
Require Export lemma__samesidereflexive.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__10.
Require Export proposition__12.
Definition lemma__notperp : forall A B C P, (euclidean__axioms.BetS A C B) -> ((euclidean__axioms.nCol A B P) -> (exists X, (euclidean__axioms.nCol A B X) /\ ((euclidean__defs.OS X P A B) /\ (~(euclidean__defs.Per A C X))))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq C B) as H1.
- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H1.
-- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
-- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
exact H2.
- assert (* Cut *) (euclidean__axioms.neq B C) as H2.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C B H1).
-- assert (* Cut *) (~(C = P)) as H3.
--- intro H3.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
---- apply (@eq__ind__r euclidean__axioms.Point P (fun C0 => (euclidean__axioms.BetS A C0 B) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.neq B C0) -> (euclidean__axioms.nCol A B C0))))) with (x := C).
-----intro H4.
intro H5.
intro H6.
exact H0.

----- exact H3.
----- exact H.
----- exact H1.
----- exact H2.
---- assert (* Cut *) (euclidean__axioms.Col A C B) as H5.
----- right.
right.
right.
right.
left.
exact H.
----- assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
------ assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H6.
------- apply (@lemma__collinearorder.lemma__collinearorder A C B H5).
------- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H13.
------ apply (@euclidean__tactics.Col__nCol__False A B C H4 H6).
--- assert (* Cut *) (exists Q, (euclidean__axioms.BetS B C Q) /\ (euclidean__axioms.Cong C Q C P)) as H4.
---- apply (@lemma__extension.lemma__extension B C C P H2 H3).
---- destruct H4 as [Q H5].
destruct H5 as [H6 H7].
assert (* Cut *) (~(P = Q)) as H8.
----- intro H8.
assert (* Cut *) (euclidean__axioms.Col B C Q) as H9.
------ right.
right.
right.
right.
left.
exact H6.
------ assert (* Cut *) (euclidean__axioms.Col B C P) as H10.
------- apply (@eq__ind__r euclidean__axioms.Point Q (fun P0 => (euclidean__axioms.nCol A B P0) -> ((~(C = P0)) -> ((euclidean__axioms.Cong C Q C P0) -> (euclidean__axioms.Col B C P0))))) with (x := P).
--------intro H10.
intro H11.
intro H12.
exact H9.

-------- exact H8.
-------- exact H0.
-------- exact H3.
-------- exact H7.
------- assert (* Cut *) (euclidean__axioms.Col A C B) as H11.
-------- right.
right.
right.
right.
left.
exact H.
-------- assert (* Cut *) (euclidean__axioms.Col C B A) as H12.
--------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H12.
---------- apply (@lemma__collinearorder.lemma__collinearorder A C B H11).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.Col C B P) as H13.
---------- assert (* Cut *) ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B))))) as H13.
----------- apply (@lemma__collinearorder.lemma__collinearorder B C P H10).
----------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H14.
---------- assert (* Cut *) (euclidean__axioms.Col B A P) as H14.
----------- apply (@euclidean__tactics.not__nCol__Col B A P).
------------intro H14.
apply (@euclidean__tactics.Col__nCol__False B A P H14).
-------------apply (@lemma__collinear4.lemma__collinear4 C B A P H12 H13 H1).


----------- assert (* Cut *) (euclidean__axioms.Col A B P) as H15.
------------ assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H15.
------------- apply (@lemma__collinearorder.lemma__collinearorder B A P H14).
------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H16.
------------ apply (@euclidean__tactics.Col__nCol__False A B P H0 H15).
----- assert (* Cut *) (exists M, (euclidean__axioms.BetS P M Q) /\ (euclidean__axioms.Cong M P M Q)) as H9.
------ apply (@proposition__10.proposition__10 P Q H8).
------ destruct H9 as [M H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__axioms.Col A C B) as H13.
------- right.
right.
right.
right.
left.
exact H.
------- assert (* Cut *) (euclidean__axioms.Col C B A) as H14.
-------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H14.
--------- apply (@lemma__collinearorder.lemma__collinearorder A C B H13).
--------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H17.
-------- assert (* Cut *) (euclidean__axioms.neq C B) as H15.
--------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P Q))) as H15.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal P M Q H11).
---------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H1.
--------- assert (* Cut *) (euclidean__axioms.Col C B Q) as H16.
---------- right.
right.
right.
left.
exact H6.
---------- assert (* Cut *) (euclidean__axioms.Col B A Q) as H17.
----------- apply (@euclidean__tactics.not__nCol__Col B A Q).
------------intro H17.
apply (@euclidean__tactics.Col__nCol__False B A Q H17).
-------------apply (@lemma__collinear4.lemma__collinear4 C B A Q H14 H16 H15).


----------- assert (* Cut *) (euclidean__axioms.Col A B Q) as H18.
------------ assert (* Cut *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col A Q B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B Q A) /\ (euclidean__axioms.Col Q A B))))) as H18.
------------- apply (@lemma__collinearorder.lemma__collinearorder B A Q H17).
------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
------------ assert (* Cut *) (euclidean__axioms.neq A B) as H19.
------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H19.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
-------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H23.
------------- assert (* Cut *) (euclidean__defs.OS P P A B) as H20.
-------------- apply (@lemma__samesidereflexive.lemma__samesidereflexive A B P H0).
-------------- assert (* Cut *) (euclidean__axioms.neq Q P) as H21.
--------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P Q H8).
--------------- assert (* Cut *) (euclidean__axioms.BetS Q M P) as H22.
---------------- apply (@euclidean__axioms.axiom__betweennesssymmetry P M Q H11).
---------------- assert (* Cut *) (euclidean__defs.Out Q P M) as H23.
----------------- apply (@lemma__ray4.lemma__ray4 Q P M).
------------------left.
exact H22.

------------------ exact H21.
----------------- assert (* Cut *) (euclidean__axioms.Col A Q B) as H24.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H24.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A B Q H18).
------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
------------------ assert (* Cut *) (euclidean__defs.OS P M A B) as H25.
------------------- apply (@lemma__sameside2.lemma__sameside2 A Q B P P M H20 H24 H23).
------------------- assert (* Cut *) (euclidean__defs.OS M P A B) as H26.
-------------------- assert (* Cut *) ((euclidean__defs.OS M P A B) /\ ((euclidean__defs.OS P M B A) /\ (euclidean__defs.OS M P B A))) as H26.
--------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B P M H25).
--------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H27.
-------------------- assert (* Cut *) (~(euclidean__axioms.Col A B M)) as H27.
--------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col B M Q) as H28.
---------------------- apply (@euclidean__tactics.not__nCol__Col B M Q).
-----------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False B M Q H28).
------------------------apply (@lemma__collinear4.lemma__collinear4 A B M Q H27 H18 H19).


---------------------- assert (* Cut *) (euclidean__axioms.Col P M Q) as H29.
----------------------- right.
right.
right.
right.
left.
exact H11.
----------------------- assert (* Cut *) (euclidean__axioms.Col M Q P) as H30.
------------------------ assert (* Cut *) ((euclidean__axioms.Col M P Q) /\ ((euclidean__axioms.Col M Q P) /\ ((euclidean__axioms.Col Q P M) /\ ((euclidean__axioms.Col P Q M) /\ (euclidean__axioms.Col Q M P))))) as H30.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder P M Q H29).
------------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H33.
------------------------ assert (* Cut *) (euclidean__axioms.Col M Q B) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.Col M B Q) /\ ((euclidean__axioms.Col M Q B) /\ ((euclidean__axioms.Col Q B M) /\ ((euclidean__axioms.Col B Q M) /\ (euclidean__axioms.Col Q M B))))) as H31.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M Q H28).
-------------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H34.
------------------------- assert (* Cut *) (euclidean__axioms.neq M Q) as H32.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq P M) /\ (euclidean__axioms.neq P Q))) as H32.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P M Q H11).
--------------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H33.
-------------------------- assert (* Cut *) (euclidean__axioms.Col Q P B) as H33.
--------------------------- apply (@euclidean__tactics.not__nCol__Col Q P B).
----------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False Q P B H33).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 M Q P B H30 H31 H32).


--------------------------- assert (* Cut *) (euclidean__axioms.Col Q B P) as H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q B P) /\ (euclidean__axioms.Col B P Q))))) as H34.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q P B H33).
----------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
---------------------------- assert (* Cut *) (euclidean__axioms.Col Q B A) as H35.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col A B Q) /\ (euclidean__axioms.Col B Q A))))) as H35.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A Q B H24).
------------------------------ destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H38.
----------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H36.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq C Q) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B Q))) as H36.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B C Q H6).
------------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H40.
------------------------------ assert (* Cut *) (euclidean__axioms.neq Q B) as H37.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B Q H36).
------------------------------- assert (* Cut *) (euclidean__axioms.Col B P A) as H38.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col B P A).
---------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False B P A H38).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 Q B P A H34 H35 H37).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col A P B))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B P A H38).
---------------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H44.
--------------------------------- apply (@euclidean__tactics.Col__nCol__False A B P H0 H39).
--------------------- assert (* Cut *) (exists R, euclidean__defs.Perp__at M R A B R) as H28.
---------------------- apply (@proposition__12.proposition__12 A B M).
-----------------------apply (@euclidean__tactics.nCol__notCol A B M H27).

---------------------- destruct H28 as [R H29].
assert (exists E, (euclidean__axioms.Col M R R) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__defs.Per E R M)))) as H30 by exact H29.
destruct H30 as [E H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
assert (* Cut *) (euclidean__defs.Per M R E) as H38.
----------------------- apply (@lemma__8__2.lemma__8__2 E R M H37).
----------------------- assert (* Cut *) (~(M = R)) as H39.
------------------------ intro H39.
assert (* Cut *) (euclidean__axioms.Col A B M) as H40.
------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun M0 => (euclidean__axioms.BetS P M0 Q) -> ((euclidean__axioms.Cong M0 P M0 Q) -> ((euclidean__axioms.BetS Q M0 P) -> ((euclidean__defs.Out Q P M0) -> ((euclidean__defs.OS P M0 A B) -> ((euclidean__defs.OS M0 P A B) -> ((~(euclidean__axioms.Col A B M0)) -> ((euclidean__defs.Perp__at M0 R A B R) -> ((euclidean__axioms.Col M0 R R) -> ((euclidean__defs.Per E R M0) -> ((euclidean__defs.Per M0 R E) -> (euclidean__axioms.Col A B M0))))))))))))) with (x := M).
--------------------------intro H40.
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
exact H34.

-------------------------- exact H39.
-------------------------- exact H11.
-------------------------- exact H12.
-------------------------- exact H22.
-------------------------- exact H23.
-------------------------- exact H25.
-------------------------- exact H26.
-------------------------- exact H27.
-------------------------- exact H29.
-------------------------- exact H32.
-------------------------- exact H37.
-------------------------- exact H38.
------------------------- apply (@H27 H40).
------------------------ assert (* Cut *) (euclidean__axioms.neq A C) as H40.
------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H40.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A C B H).
-------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H43.
------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H41.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H41.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B A H14).
--------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
-------------------------- assert (* Cut *) (~(euclidean__defs.Per A C M)) as H42.
--------------------------- intro H42.
assert (* Cut *) (~(euclidean__axioms.neq R C)) as H43.
---------------------------- intro H43.
assert (* Cut *) (euclidean__axioms.Col B A C) as H44.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H44.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A B C H41).
------------------------------ destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H45.
----------------------------- assert (* Cut *) (euclidean__axioms.Col B A R) as H45.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col B R A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A R B) /\ (euclidean__axioms.Col R B A))))) as H45.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B R H34).
------------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H46.
------------------------------ assert (* Cut *) (euclidean__axioms.neq B A) as H46.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H19).
------------------------------- assert (* Cut *) (euclidean__axioms.Col A C R) as H47.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col A C R).
---------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False A C R H47).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 B A C R H44 H45 H46).


-------------------------------- assert (* Cut *) (euclidean__defs.Per R C M) as H48.
--------------------------------- apply (@lemma__collinearright.lemma__collinearright A C R M H42 H47 H43).
--------------------------------- assert (* Cut *) (~(euclidean__defs.Per M R C)) as H49.
---------------------------------- apply (@lemma__8__7.lemma__8__7 M C R H48).
---------------------------------- assert (euclidean__defs.Per E R M) as H50 by exact H37.
assert (* Cut *) (euclidean__axioms.Col B C R) as H51.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col B C R).
------------------------------------intro H51.
apply (@euclidean__tactics.Col__nCol__False B C R H51).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 A B C R H41 H34 H19).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H52.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col B C E).
-------------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False B C E H52).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 A B C E H41 H36 H19).


------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H53.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M P) /\ ((euclidean__axioms.neq Q M) /\ (euclidean__axioms.neq Q P))) as H53.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q M P H22).
-------------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H15.
------------------------------------- assert (euclidean__axioms.neq B C) as H54 by exact H2.
assert (* Cut *) (euclidean__axioms.Col C R E) as H55.
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col C R E).
---------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False C R E H55).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 B C R E H51 H52 H54).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E R C) as H56.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R C E) /\ ((euclidean__axioms.Col R E C) /\ ((euclidean__axioms.Col E C R) /\ ((euclidean__axioms.Col C E R) /\ (euclidean__axioms.Col E R C))))) as H56.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C R E H55).
---------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq C R) as H57.
---------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric R C H43).
---------------------------------------- assert (* Cut *) (euclidean__defs.Per C R M) as H58.
----------------------------------------- apply (@lemma__collinearright.lemma__collinearright E R C M H50 H56 H57).
----------------------------------------- assert (* Cut *) (euclidean__defs.Per M R C) as H59.
------------------------------------------ apply (@lemma__8__2.lemma__8__2 C R M H58).
------------------------------------------ apply (@H27).
-------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B M).
--------------------------------------------intro H60.
apply (@H49 H59).


---------------------------- assert (* Cut *) (~(M = C)) as H44.
----------------------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col A B M) as H45.
------------------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun M0 => (euclidean__axioms.BetS P M0 Q) -> ((euclidean__axioms.Cong M0 P M0 Q) -> ((euclidean__axioms.BetS Q M0 P) -> ((euclidean__defs.Out Q P M0) -> ((euclidean__defs.OS P M0 A B) -> ((euclidean__defs.OS M0 P A B) -> ((~(euclidean__axioms.Col A B M0)) -> ((euclidean__defs.Perp__at M0 R A B R) -> ((euclidean__axioms.Col M0 R R) -> ((euclidean__defs.Per E R M0) -> ((euclidean__defs.Per M0 R E) -> ((~(M0 = R)) -> ((euclidean__defs.Per A C M0) -> (euclidean__axioms.Col A B M0))))))))))))))) with (x := M).
-------------------------------intro H45.
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
exact H41.

------------------------------- exact H44.
------------------------------- exact H11.
------------------------------- exact H12.
------------------------------- exact H22.
------------------------------- exact H23.
------------------------------- exact H25.
------------------------------- exact H26.
------------------------------- exact H27.
------------------------------- exact H29.
------------------------------- exact H32.
------------------------------- exact H37.
------------------------------- exact H38.
------------------------------- exact H39.
------------------------------- exact H42.
------------------------------ apply (@H27 H45).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong Q C P C) as H45.
------------------------------ assert (* Cut *) ((euclidean__axioms.Cong Q C P C) /\ ((euclidean__axioms.Cong Q C C P) /\ (euclidean__axioms.Cong C Q P C))) as H45.
------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip C Q C P H7).
------------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
------------------------------ assert (euclidean__axioms.BetS Q M P) as H46 by exact H22.
assert (* Cut *) (euclidean__axioms.Cong Q M P M) as H47.
------------------------------- assert (* Cut *) ((euclidean__axioms.Cong Q M P M) /\ (euclidean__axioms.Cong P M Q M)) as H47.
-------------------------------- apply (@lemma__doublereverse.lemma__doublereverse M P M Q H12).
-------------------------------- destruct H47 as [H48 H49].
exact H48.
------------------------------- assert (* Cut *) (euclidean__defs.Per Q M C) as H48.
-------------------------------- exists P.
split.
--------------------------------- exact H46.
--------------------------------- split.
---------------------------------- exact H47.
---------------------------------- split.
----------------------------------- exact H45.
----------------------------------- exact H44.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq C Q) as H49.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq C Q) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B Q))) as H49.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B C Q H6).
---------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H50.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq Q C) as H50.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C Q H49).
---------------------------------- assert (euclidean__defs.Per E R M) as H51 by exact H37.
assert (* Cut *) (euclidean__axioms.neq Q R) as H52.
----------------------------------- assert (* Cut *) (R = C) as H52.
------------------------------------ apply (@euclidean__tactics.NNPP (R = C) H43).
------------------------------------ intro H53.
assert (* Cut *) (C = Q) as Heq.
------------------------------------- apply (@logic.eq__trans Point C R Q).
--------------------------------------apply (@logic.eq__sym Point R C H52).

--------------------------------------apply (@logic.eq__sym Point Q R H53).

------------------------------------- assert False.
--------------------------------------apply (@H49 Heq).
-------------------------------------- contradiction.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B C Q) as H53.
------------------------------------ right.
right.
right.
right.
left.
exact H6.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B Q) as H54.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B Q) /\ ((euclidean__axioms.Col C Q B) /\ ((euclidean__axioms.Col Q B C) /\ ((euclidean__axioms.Col B Q C) /\ (euclidean__axioms.Col Q C B))))) as H54.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C Q H53).
-------------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H55.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q B C) as H55.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C Q) /\ ((euclidean__axioms.Col B Q C) /\ ((euclidean__axioms.Col Q C B) /\ ((euclidean__axioms.Col C Q B) /\ (euclidean__axioms.Col Q B C))))) as H55.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B Q H54).
--------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H63.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E R) as H56.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col B E R).
----------------------------------------intro H56.
apply (@euclidean__tactics.Col__nCol__False B E R H56).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 A B E R H36 H34 H19).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E Q) as H57.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col B E Q).
-----------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False B E Q H57).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A B E Q H36 H18 H19).


---------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq B E)) as H58.
----------------------------------------- intro H58.
assert (* Cut *) (euclidean__axioms.Col E R Q) as H59.
------------------------------------------ apply (@euclidean__tactics.not__nCol__Col E R Q).
-------------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False E R Q H59).
--------------------------------------------apply (@lemma__collinear4.lemma__collinear4 B E R Q H56 H57 H58).


------------------------------------------ assert (* Cut *) (euclidean__defs.Per Q R M) as H60.
------------------------------------------- apply (@lemma__collinearright.lemma__collinearright E R Q M H51 H59 H52).
------------------------------------------- assert (* Cut *) (euclidean__defs.Per Q C M) as H61.
-------------------------------------------- apply (@eq__ind euclidean__axioms.Point R (fun X => euclidean__defs.Per Q X M)) with (y := C).
--------------------------------------------- exact H60.
---------------------------------------------apply (@euclidean__tactics.NNPP (R = C) H43).

-------------------------------------------- assert (* Cut *) (euclidean__defs.Per M C Q) as H62.
--------------------------------------------- apply (@lemma__8__2.lemma__8__2 Q C M H61).
--------------------------------------------- assert (* Cut *) (~(euclidean__defs.Per Q M C)) as H63.
---------------------------------------------- apply (@lemma__8__7.lemma__8__7 Q C M H62).
---------------------------------------------- apply (@H27).
-----------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B M).
------------------------------------------------intro H64.
apply (@H63 H48).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E R) as H59.
------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun X => euclidean__axioms.Col A E X)) with (x := R).
-------------------------------------------apply (@eq__ind euclidean__axioms.Point B (fun X => euclidean__axioms.Col A X C)) with (y := E).
-------------------------------------------- exact H41.
--------------------------------------------apply (@euclidean__tactics.NNPP (B = E) H58).


-------------------------------------------apply (@euclidean__tactics.NNPP (R = C) H43).

------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B Q) as H60.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A R) /\ ((euclidean__axioms.Col E R A) /\ ((euclidean__axioms.Col R A E) /\ ((euclidean__axioms.Col A R E) /\ (euclidean__axioms.Col R E A))))) as H60.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A E R H59).
-------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H18.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E Q) as H61.
-------------------------------------------- apply (@eq__ind euclidean__axioms.Point B (fun X => euclidean__axioms.Col A X Q)) with (y := E).
--------------------------------------------- exact H60.
---------------------------------------------apply (@euclidean__tactics.NNPP (B = E) H58).

-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H62.
--------------------------------------------- assert (* Cut *) (B = E) as H62.
---------------------------------------------- apply (@euclidean__tactics.NNPP (B = E) H58).
---------------------------------------------- assert (* Cut *) (R = C) as H63.
----------------------------------------------- apply (@euclidean__tactics.NNPP (R = C) H43).
----------------------------------------------- intro H64.
assert (* Cut *) (A = B) as Heq.
------------------------------------------------ apply (@logic.eq__trans Point A E B H64).
-------------------------------------------------apply (@logic.eq__sym Point B E H62).

------------------------------------------------ assert False.
-------------------------------------------------apply (@H19 Heq).
------------------------------------------------- contradiction.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E R Q) as H63.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E R Q).
-----------------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False E R Q H63).
------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A E R Q H59 H61 H62).


---------------------------------------------- assert (* Cut *) (euclidean__defs.Per Q R M) as H64.
----------------------------------------------- apply (@lemma__collinearright.lemma__collinearright E R Q M H51 H63 H52).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Per Q C M) as H65.
------------------------------------------------ apply (@eq__ind euclidean__axioms.Point R (fun X => euclidean__defs.Per Q X M)) with (y := C).
------------------------------------------------- exact H64.
-------------------------------------------------apply (@euclidean__tactics.NNPP (R = C) H43).

------------------------------------------------ assert (* Cut *) (euclidean__defs.Per M C Q) as H66.
------------------------------------------------- apply (@lemma__8__2.lemma__8__2 Q C M H65).
------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Per Q M C)) as H67.
-------------------------------------------------- apply (@lemma__8__7.lemma__8__7 Q C M H66).
-------------------------------------------------- apply (@H27).
---------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B M).
----------------------------------------------------intro H68.
apply (@H67 H48).


--------------------------- exists M.
split.
---------------------------- apply (@euclidean__tactics.nCol__notCol A B M H27).
---------------------------- split.
----------------------------- exact H26.
----------------------------- exact H42.
Qed.
