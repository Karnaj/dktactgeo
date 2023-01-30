Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7a.
Require Export lemma__angleordertransitive.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoffunique.
Require Export lemma__ray3.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__sameside2.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__07.
Definition lemma__angletrichotomy : forall A B C D E F, (euclidean__defs.LtA A B C D E F) -> (~(euclidean__defs.LtA D E F A B C)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
assert (* Cut *) (~(euclidean__defs.LtA D E F A B C)) as H0.
- intro H0.
assert (* Cut *) (euclidean__defs.LtA A B C A B C) as H1.
-- apply (@lemma__angleordertransitive.lemma__angleordertransitive A B C D E F A B C H H0).
-- assert (exists G H2 J, (euclidean__axioms.BetS G H2 J) /\ ((euclidean__defs.Out B A G) /\ ((euclidean__defs.Out B C J) /\ (euclidean__defs.CongA A B C A B H2)))) as H2 by exact H1.
destruct H2 as [G H3].
destruct H3 as [H4 H5].
destruct H5 as [J H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B H4 v) /\ ((euclidean__axioms.Cong B U B u) /\ ((euclidean__axioms.Cong B V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H13 by exact H12.
destruct H13 as [U H14].
destruct H14 as [V H15].
destruct H15 as [u H16].
destruct H16 as [v H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
assert (* Cut *) (~(A = B)) as H32.
--- intro H32.
assert (* Cut *) (euclidean__axioms.Col A B C) as H33.
---- left.
exact H32.
---- apply (@euclidean__tactics.Col__nCol__False A B C H31 H33).
--- assert (* Cut *) (euclidean__axioms.neq B A) as H33.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H32).
---- assert (* Cut *) (U = u) as H34.
----- apply (@lemma__layoffunique.lemma__layoffunique B A U u H18 H22 H26).
----- assert (* Cut *) (euclidean__axioms.Cong U V U v) as H35.
------ apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> (euclidean__axioms.Cong U0 V U0 v))))) with (x := U).
-------intro H35.
intro H36.
intro H37.
exact H37.

------- exact H34.
------- exact H18.
------- exact H26.
------- exact H30.
------ assert (* Cut *) (euclidean__axioms.Col B A U) as H36.
------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B A U H18).
------- assert (* Cut *) (euclidean__axioms.Col B A G) as H37.
-------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B A G H9).
-------- assert (* Cut *) (euclidean__axioms.neq G H4) as H38.
--------- assert (* Cut *) ((euclidean__axioms.neq H4 J) /\ ((euclidean__axioms.neq G H4) /\ (euclidean__axioms.neq G J))) as H38.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal G H4 J H7).
---------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
--------- assert (* Cut *) (euclidean__axioms.neq H4 G) as H39.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G H4 H38).
---------- assert (* Cut *) (exists P, (euclidean__axioms.BetS H4 G P) /\ (euclidean__axioms.Cong G P H4 G)) as H40.
----------- apply (@lemma__extension.lemma__extension H4 G H4 G H39 H39).
----------- destruct H40 as [P H41].
destruct H41 as [H42 H43].
assert (* Cut *) (euclidean__axioms.BetS J H4 G) as H44.
------------ apply (@euclidean__axioms.axiom__betweennesssymmetry G H4 J H7).
------------ assert (* Cut *) (euclidean__axioms.BetS J G P) as H45.
------------- apply (@lemma__3__7a.lemma__3__7a J H4 G P H44 H42).
------------- assert (* Cut *) (~(euclidean__axioms.Col B A J)) as H46.
-------------- intro H46.
assert (* Cut *) (euclidean__axioms.Col B C J) as H47.
--------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B C J H11).
--------------- assert (* Cut *) (euclidean__axioms.Col J B A) as H48.
---------------- assert (* Cut *) ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B))))) as H48.
----------------- apply (@lemma__collinearorder.lemma__collinearorder B A J H46).
----------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
---------------- assert (* Cut *) (euclidean__axioms.Col J B C) as H49.
----------------- assert (* Cut *) ((euclidean__axioms.Col C B J) /\ ((euclidean__axioms.Col C J B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B J C) /\ (euclidean__axioms.Col J C B))))) as H49.
------------------ apply (@lemma__collinearorder.lemma__collinearorder B C J H47).
------------------ destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H54.
----------------- assert (* Cut *) (euclidean__axioms.neq B J) as H50.
------------------ apply (@lemma__raystrict.lemma__raystrict B C J H11).
------------------ assert (* Cut *) (euclidean__axioms.neq J B) as H51.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B J H50).
------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H52.
-------------------- apply (@euclidean__tactics.not__nCol__Col B A C).
---------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False B A C H52).
----------------------apply (@lemma__collinear4.lemma__collinear4 J B A C H48 H49 H51).


-------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H53.
--------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H53.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H52).
---------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H54.
--------------------- apply (@euclidean__tactics.Col__nCol__False A B C H31 H53).
-------------- assert (* Cut *) (euclidean__axioms.TS J B A P) as H47.
--------------- exists G.
split.
---------------- exact H45.
---------------- split.
----------------- exact H37.
----------------- apply (@euclidean__tactics.nCol__notCol B A J H46).
--------------- assert (* Cut *) (~(euclidean__axioms.Col B U H4)) as H48.
---------------- intro H48.
assert (* Cut *) (euclidean__axioms.Col B A U) as H49.
----------------- apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> ((euclidean__axioms.Cong U0 V U0 v) -> ((euclidean__axioms.Col B A U0) -> ((euclidean__axioms.Col B U0 H4) -> (euclidean__axioms.Col B A U0)))))))) with (x := U).
------------------intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
exact H53.

------------------ exact H34.
------------------ exact H18.
------------------ exact H26.
------------------ exact H30.
------------------ exact H35.
------------------ exact H36.
------------------ exact H48.
----------------- assert (* Cut *) (euclidean__axioms.Col U B A) as H50.
------------------ assert (* Cut *) ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))))) as H50.
------------------- apply (@lemma__collinearorder.lemma__collinearorder B A U H49).
------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H55.
------------------ assert (* Cut *) (euclidean__axioms.Col U B H4) as H51.
------------------- assert (* Cut *) ((euclidean__axioms.Col U B H4) /\ ((euclidean__axioms.Col U H4 B) /\ ((euclidean__axioms.Col H4 B U) /\ ((euclidean__axioms.Col B H4 U) /\ (euclidean__axioms.Col H4 U B))))) as H51.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B U H4 H48).
-------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H52.
------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H52.
-------------------- apply (@lemma__raystrict.lemma__raystrict B A U H18).
-------------------- assert (* Cut *) (euclidean__axioms.neq U B) as H53.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B U H52).
--------------------- assert (* Cut *) (euclidean__axioms.Col B A H4) as H54.
---------------------- apply (@euclidean__tactics.not__nCol__Col B A H4).
-----------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False B A H4 H54).
------------------------apply (@lemma__collinear4.lemma__collinear4 U B A H4 H50 H51 H53).


---------------------- assert (* Cut *) (euclidean__axioms.Col G H4 J) as H55.
----------------------- right.
right.
right.
right.
left.
exact H7.
----------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H56.
------------------------ assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H56.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A G H37).
------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H57.
------------------------ assert (* Cut *) (euclidean__axioms.Col A B H4) as H57.
------------------------- assert (* Cut *) ((euclidean__axioms.Col A B H4) /\ ((euclidean__axioms.Col A H4 B) /\ ((euclidean__axioms.Col H4 B A) /\ ((euclidean__axioms.Col B H4 A) /\ (euclidean__axioms.Col H4 A B))))) as H57.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A H4 H54).
-------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H58.
------------------------- assert (* Cut *) (euclidean__axioms.Col B G H4) as H58.
-------------------------- apply (@euclidean__tactics.not__nCol__Col B G H4).
---------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False B G H4 H58).
----------------------------apply (@lemma__collinear4.lemma__collinear4 A B G H4 H56 H57 H32).


-------------------------- assert (* Cut *) (euclidean__axioms.Col G H4 B) as H59.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col G B H4) /\ ((euclidean__axioms.Col G H4 B) /\ ((euclidean__axioms.Col H4 B G) /\ ((euclidean__axioms.Col B H4 G) /\ (euclidean__axioms.Col H4 G B))))) as H59.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder B G H4 H58).
---------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
--------------------------- assert (euclidean__axioms.Col G H4 J) as H60 by exact H55.
assert (* Cut *) (euclidean__axioms.neq G H4) as H61.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq G P) /\ ((euclidean__axioms.neq J G) /\ (euclidean__axioms.neq J P))) as H61.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal J G P H45).
----------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H38.
---------------------------- assert (* Cut *) (euclidean__axioms.Col H4 B J) as H62.
----------------------------- apply (@euclidean__tactics.not__nCol__Col H4 B J).
------------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False H4 B J H62).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 G H4 B J H59 H60 H61).


----------------------------- assert (* Cut *) (euclidean__axioms.Col H4 B A) as H63.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A H4) /\ ((euclidean__axioms.Col B H4 A) /\ ((euclidean__axioms.Col H4 A B) /\ ((euclidean__axioms.Col A H4 B) /\ (euclidean__axioms.Col H4 B A))))) as H63.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B H4 H57).
------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H71.
------------------------------ assert (* Cut *) (~(euclidean__axioms.neq H4 B)) as H64.
------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.Col B J A) as H65.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col B J A).
---------------------------------intro H65.
apply (@H46).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 H4 B A J H63 H62 H64).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col B A J) as H66.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col J A B) /\ ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col B A J) /\ (euclidean__axioms.Col A J B))))) as H66.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B J A H65).
---------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
--------------------------------- apply (@H46 H66).
------------------------------- assert (* Cut *) (euclidean__axioms.BetS G B J) as H65.
-------------------------------- apply (@eq__ind euclidean__axioms.Point H4 (fun X => euclidean__axioms.BetS G X J)) with (y := B).
--------------------------------- exact H7.
---------------------------------apply (@euclidean__tactics.NNPP (H4 = B) H64).

-------------------------------- assert (* Cut *) (euclidean__axioms.Col G B J) as H66.
--------------------------------- right.
right.
right.
right.
left.
exact H65.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B G J) as H67.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col B G J) /\ ((euclidean__axioms.Col B J G) /\ ((euclidean__axioms.Col J G B) /\ ((euclidean__axioms.Col G J B) /\ (euclidean__axioms.Col J B G))))) as H67.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G B J H66).
----------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H68.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H68.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H68.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A B G H56).
------------------------------------ destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H71.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H69.
------------------------------------ apply (@lemma__raystrict.lemma__raystrict B A G H9).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col G J A) as H70.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col G J A).
--------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False G J A H70).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 B G J A H67 H68 H69).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col G J B) as H71.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G B J) /\ ((euclidean__axioms.Col G J B) /\ ((euclidean__axioms.Col J B G) /\ ((euclidean__axioms.Col B J G) /\ (euclidean__axioms.Col J G B))))) as H71.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B G J H67).
--------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H74.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq G J) as H72.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B J) /\ ((euclidean__axioms.neq G B) /\ (euclidean__axioms.neq G J))) as H72.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G B J H65).
---------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col J A B) as H73.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col J A B).
-----------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False J A B H73).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G J A B H70 H71 H72).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A J) as H74.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col J B A) /\ (euclidean__axioms.Col B A J))))) as H74.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder J A B H73).
------------------------------------------ destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H82.
----------------------------------------- apply (@H46 H74).
---------------- assert (* Cut *) (euclidean__defs.Out B G U) as H49.
----------------- apply (@lemma__ray3.lemma__ray3 B A G U H9 H18).
----------------- assert (* Cut *) (euclidean__axioms.Col B G U) as H50.
------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B G U H49).
------------------ assert (* Cut *) (euclidean__axioms.Col B U G) as H51.
------------------- assert (* Cut *) ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G U B) /\ ((euclidean__axioms.Col U B G) /\ ((euclidean__axioms.Col B U G) /\ (euclidean__axioms.Col U G B))))) as H51.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B G U H50).
-------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H58.
------------------- assert (* Cut *) (euclidean__axioms.TS H4 B U P) as H52.
-------------------- exists G.
split.
--------------------- exact H42.
--------------------- split.
---------------------- exact H51.
---------------------- apply (@euclidean__tactics.nCol__notCol B U H4 H48).
-------------------- assert (* Cut *) (euclidean__axioms.BetS J H4 G) as H53.
--------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> ((euclidean__axioms.Cong U0 V U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> (euclidean__axioms.BetS J H4 G)))))))))))) with (x := U).
----------------------intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
exact H44.

---------------------- exact H34.
---------------------- exact H18.
---------------------- exact H26.
---------------------- exact H30.
---------------------- exact H35.
---------------------- exact H36.
---------------------- exact H48.
---------------------- exact H49.
---------------------- exact H50.
---------------------- exact H51.
---------------------- exact H52.
--------------------- assert (* Cut *) (euclidean__axioms.BetS J G P) as H54.
---------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> ((euclidean__axioms.Cong U0 V U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> (euclidean__axioms.BetS J G P)))))))))))) with (x := U).
-----------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
exact H45.

----------------------- exact H34.
----------------------- exact H18.
----------------------- exact H26.
----------------------- exact H30.
----------------------- exact H35.
----------------------- exact H36.
----------------------- exact H48.
----------------------- exact H49.
----------------------- exact H50.
----------------------- exact H51.
----------------------- exact H52.
---------------------- assert (* Cut *) (~(euclidean__axioms.Col B U J)) as H55.
----------------------- intro H55.
assert (* Cut *) (euclidean__axioms.Col B C J) as H56.
------------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B C J H11).
------------------------ assert (* Cut *) (euclidean__axioms.Col B J C) as H57.
------------------------- assert (* Cut *) ((euclidean__axioms.Col C B J) /\ ((euclidean__axioms.Col C J B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B J C) /\ (euclidean__axioms.Col J C B))))) as H57.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C J H56).
-------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H64.
------------------------- assert (* Cut *) (euclidean__axioms.Col B A U) as H58.
-------------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> ((euclidean__axioms.Cong U0 V U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> ((euclidean__axioms.Col B U0 J) -> (euclidean__axioms.Col B A U0))))))))))))) with (x := U).
---------------------------intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
exact H62.

--------------------------- exact H34.
--------------------------- exact H18.
--------------------------- exact H26.
--------------------------- exact H30.
--------------------------- exact H35.
--------------------------- exact H36.
--------------------------- exact H48.
--------------------------- exact H49.
--------------------------- exact H50.
--------------------------- exact H51.
--------------------------- exact H52.
--------------------------- exact H55.
-------------------------- assert (* Cut *) (euclidean__axioms.Col U B A) as H59.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))))) as H59.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A U H58).
---------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H64.
--------------------------- assert (* Cut *) (euclidean__axioms.Col U B J) as H60.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col U B J) /\ ((euclidean__axioms.Col U J B) /\ ((euclidean__axioms.Col J B U) /\ ((euclidean__axioms.Col B J U) /\ (euclidean__axioms.Col J U B))))) as H60.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B U J H55).
----------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H61.
---------------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H61.
----------------------------- apply (@lemma__raystrict.lemma__raystrict B G U H49).
----------------------------- assert (* Cut *) (euclidean__axioms.neq U B) as H62.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B U H61).
------------------------------ assert (* Cut *) (euclidean__axioms.Col B A J) as H63.
------------------------------- apply (@euclidean__tactics.not__nCol__Col B A J).
--------------------------------intro H63.
apply (@H46).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 U B A J H59 H60 H62).


------------------------------- assert (* Cut *) (euclidean__axioms.Col B C J) as H64.
-------------------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 V u v) -> ((euclidean__axioms.Cong U0 V U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> ((euclidean__axioms.Col B U0 J) -> ((euclidean__axioms.Col B A U0) -> ((euclidean__axioms.Col U0 B A) -> ((euclidean__axioms.Col U0 B J) -> ((euclidean__axioms.neq B U0) -> ((euclidean__axioms.neq U0 B) -> (euclidean__axioms.Col B C J)))))))))))))))))) with (x := U).
---------------------------------intro H64.
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
exact H56.

--------------------------------- exact H34.
--------------------------------- exact H18.
--------------------------------- exact H26.
--------------------------------- exact H30.
--------------------------------- exact H35.
--------------------------------- exact H36.
--------------------------------- exact H48.
--------------------------------- exact H49.
--------------------------------- exact H50.
--------------------------------- exact H51.
--------------------------------- exact H52.
--------------------------------- exact H55.
--------------------------------- exact H58.
--------------------------------- exact H59.
--------------------------------- exact H60.
--------------------------------- exact H61.
--------------------------------- exact H62.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col J B C) as H65.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B J) /\ ((euclidean__axioms.Col C J B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B J C) /\ (euclidean__axioms.Col J C B))))) as H65.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C J H64).
---------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H70.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col J B A) as H66.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B J) /\ ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J B A) /\ ((euclidean__axioms.Col B J A) /\ (euclidean__axioms.Col J A B))))) as H66.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A J H63).
----------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H71.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq B J) as H67.
----------------------------------- apply (@lemma__raystrict.lemma__raystrict B C J H11).
----------------------------------- assert (* Cut *) (euclidean__axioms.neq J B) as H68.
------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B J H67).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C A) as H69.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col B C A).
--------------------------------------intro H69.
apply (@H46 H63).

------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H70.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H70.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C A H69).
--------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H75.
-------------------------------------- apply (@H46 H63).
----------------------- assert (* Cut *) (euclidean__defs.OS J H4 B U) as H56.
------------------------ exists P.
exists G.
exists G.
split.
------------------------- exact H51.
------------------------- split.
-------------------------- exact H51.
-------------------------- split.
--------------------------- exact H54.
--------------------------- split.
---------------------------- exact H42.
---------------------------- split.
----------------------------- apply (@euclidean__tactics.nCol__notCol B U J H55).
----------------------------- apply (@euclidean__tactics.nCol__notCol B U H4 H48).
------------------------ assert (* Cut *) (euclidean__defs.OS H4 J B U) as H57.
------------------------- assert (* Cut *) ((euclidean__defs.OS H4 J B U) /\ ((euclidean__defs.OS J H4 U B) /\ (euclidean__defs.OS H4 J U B))) as H57.
-------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric B U J H4 H56).
-------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H58.
------------------------- assert (* Cut *) (euclidean__defs.Out B J V) as H58.
-------------------------- apply (@lemma__ray3.lemma__ray3 B C J V H11 H20).
-------------------------- assert (* Cut *) (B = B) as H59.
--------------------------- apply (@logic.eq__refl Point B).
--------------------------- assert (* Cut *) (euclidean__axioms.Col B B U) as H60.
---------------------------- left.
exact H59.
---------------------------- assert (* Cut *) (euclidean__defs.OS H4 V B U) as H61.
----------------------------- apply (@lemma__sameside2.lemma__sameside2 B B U H4 J V H57 H60 H58).
----------------------------- assert (* Cut *) (euclidean__defs.OS V H4 B U) as H62.
------------------------------ assert (* Cut *) ((euclidean__defs.OS V H4 B U) /\ ((euclidean__defs.OS H4 V U B) /\ (euclidean__defs.OS V H4 U B))) as H62.
------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric B U H4 V H61).
------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H63.
------------------------------ assert (* Cut *) (euclidean__defs.OS V v B U) as H63.
------------------------------- apply (@lemma__sameside2.lemma__sameside2 B B U V H4 v H62 H60 H24).
------------------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H64.
-------------------------------- apply (@lemma__raystrict.lemma__raystrict B G U H49).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong V B v B) as H65.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Cong V B v B) /\ ((euclidean__axioms.Cong V B B v) /\ (euclidean__axioms.Cong B V v B))) as H65.
---------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B V B v H28).
---------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong V U v U) as H66.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong V U v U) /\ ((euclidean__axioms.Cong V U U v) /\ (euclidean__axioms.Cong U V v U))) as H66.
----------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip U V U v H35).
----------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H67.
---------------------------------- assert (* Cut *) (V = v) as H67.
----------------------------------- apply (@proposition__07.proposition__07 B U V v H64 H65 H66 H63).
----------------------------------- assert (* Cut *) (euclidean__defs.Out B H4 V) as H68.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point v (fun V0 => (euclidean__defs.Out B C V0) -> ((euclidean__axioms.Cong B V0 B v) -> ((euclidean__axioms.Cong U V0 u v) -> ((euclidean__axioms.Cong U V0 U v) -> ((euclidean__defs.Out B J V0) -> ((euclidean__defs.OS H4 V0 B U) -> ((euclidean__defs.OS V0 H4 B U) -> ((euclidean__defs.OS V0 v B U) -> ((euclidean__axioms.Cong V0 B v B) -> ((euclidean__axioms.Cong V0 U v U) -> (euclidean__defs.Out B H4 V0)))))))))))) with (x := V).
-------------------------------------intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 v u v) -> ((euclidean__axioms.Cong U0 v U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> ((~(euclidean__axioms.Col B U0 J)) -> ((euclidean__defs.OS J H4 B U0) -> ((euclidean__defs.OS H4 J B U0) -> ((euclidean__axioms.Col B B U0) -> ((euclidean__defs.OS v v B U0) -> ((euclidean__defs.OS v H4 B U0) -> ((euclidean__defs.OS H4 v B U0) -> ((euclidean__axioms.neq B U0) -> ((euclidean__axioms.Cong v U0 v U0) -> (euclidean__defs.Out B H4 v))))))))))))))))))))) with (x := U).
--------------------------------------intro H78.
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
intro H95.
intro H96.
exact H24.

-------------------------------------- exact H34.
-------------------------------------- exact H18.
-------------------------------------- exact H26.
-------------------------------------- exact H70.
-------------------------------------- exact H71.
-------------------------------------- exact H36.
-------------------------------------- exact H48.
-------------------------------------- exact H49.
-------------------------------------- exact H50.
-------------------------------------- exact H51.
-------------------------------------- exact H52.
-------------------------------------- exact H55.
-------------------------------------- exact H56.
-------------------------------------- exact H57.
-------------------------------------- exact H60.
-------------------------------------- exact H75.
-------------------------------------- exact H74.
-------------------------------------- exact H73.
-------------------------------------- exact H64.
-------------------------------------- exact H77.

------------------------------------- exact H67.
------------------------------------- exact H20.
------------------------------------- exact H28.
------------------------------------- exact H30.
------------------------------------- exact H35.
------------------------------------- exact H58.
------------------------------------- exact H61.
------------------------------------- exact H62.
------------------------------------- exact H63.
------------------------------------- exact H65.
------------------------------------- exact H66.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B H4 V) as H69.
------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B H4 V H68).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col B J V) as H70.
-------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B J V H58).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col V B J) as H71.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J B V) /\ ((euclidean__axioms.Col J V B) /\ ((euclidean__axioms.Col V B J) /\ ((euclidean__axioms.Col B V J) /\ (euclidean__axioms.Col V J B))))) as H71.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B J V H70).
---------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H76.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col V B H4) as H72.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H4 B V) /\ ((euclidean__axioms.Col H4 V B) /\ ((euclidean__axioms.Col V B H4) /\ ((euclidean__axioms.Col B V H4) /\ (euclidean__axioms.Col V H4 B))))) as H72.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B H4 V H69).
----------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq B V) as H73.
----------------------------------------- apply (@lemma__raystrict.lemma__raystrict B H4 V H68).
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq V B) as H74.
------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B V H73).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B J H4) as H75.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col B J H4).
--------------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False B J H4 H75).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 V B J H4 H71 H72 H74).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H4 J) as H76.
-------------------------------------------- right.
right.
right.
right.
left.
exact H7.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H4 J B) as H77.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J B H4) /\ ((euclidean__axioms.Col J H4 B) /\ ((euclidean__axioms.Col H4 B J) /\ ((euclidean__axioms.Col B H4 J) /\ (euclidean__axioms.Col H4 J B))))) as H77.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B J H4 H75).
---------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H85.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H4 J G) as H78.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H4 G J) /\ ((euclidean__axioms.Col H4 J G) /\ ((euclidean__axioms.Col J G H4) /\ ((euclidean__axioms.Col G J H4) /\ (euclidean__axioms.Col J H4 G))))) as H78.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G H4 J H76).
----------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H81.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J H4) as H79.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H4 G) /\ ((euclidean__axioms.neq J H4) /\ (euclidean__axioms.neq J G))) as H79.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal J H4 G H53).
------------------------------------------------ destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H82.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H4 J) as H80.
------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric J H4 H79).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col J B G) as H81.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col J B G).
--------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False J B G H81).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H4 J B G H77 H78 H80).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C J) as H82.
-------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B C J H11).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J B C) as H83.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B J) /\ ((euclidean__axioms.Col C J B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B J C) /\ (euclidean__axioms.Col J C B))))) as H83.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C J H82).
---------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H88.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B J) as H84.
---------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict B C J H11).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J B) as H85.
----------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B J H84).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B G C) as H86.
------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col B G C).
-------------------------------------------------------intro H86.
apply (@euclidean__tactics.Col__nCol__False B G C H86).
--------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 J B G C H81 H83 H85).


------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G B C) as H87.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B))))) as H87.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B G C H86).
-------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H88.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A G) as H88.
-------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point v (fun V0 => (euclidean__defs.Out B C V0) -> ((euclidean__axioms.Cong B V0 B v) -> ((euclidean__axioms.Cong U V0 u v) -> ((euclidean__axioms.Cong U V0 U v) -> ((euclidean__defs.Out B J V0) -> ((euclidean__defs.OS H4 V0 B U) -> ((euclidean__defs.OS V0 H4 B U) -> ((euclidean__defs.OS V0 v B U) -> ((euclidean__axioms.Cong V0 B v B) -> ((euclidean__axioms.Cong V0 U v U) -> ((euclidean__defs.Out B H4 V0) -> ((euclidean__axioms.Col B H4 V0) -> ((euclidean__axioms.Col B J V0) -> ((euclidean__axioms.Col V0 B J) -> ((euclidean__axioms.Col V0 B H4) -> ((euclidean__axioms.neq B V0) -> ((euclidean__axioms.neq V0 B) -> (euclidean__axioms.Col B A G))))))))))))))))))) with (x := V).
---------------------------------------------------------intro H88.
intro H89.
intro H90.
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
apply (@eq__ind__r euclidean__axioms.Point u (fun U0 => (euclidean__defs.Out B A U0) -> ((euclidean__axioms.Cong B U0 B u) -> ((euclidean__axioms.Cong U0 v u v) -> ((euclidean__axioms.Cong U0 v U0 v) -> ((euclidean__axioms.Col B A U0) -> ((~(euclidean__axioms.Col B U0 H4)) -> ((euclidean__defs.Out B G U0) -> ((euclidean__axioms.Col B G U0) -> ((euclidean__axioms.Col B U0 G) -> ((euclidean__axioms.TS H4 B U0 P) -> ((~(euclidean__axioms.Col B U0 J)) -> ((euclidean__defs.OS J H4 B U0) -> ((euclidean__defs.OS H4 J B U0) -> ((euclidean__axioms.Col B B U0) -> ((euclidean__defs.OS v v B U0) -> ((euclidean__defs.OS v H4 B U0) -> ((euclidean__defs.OS H4 v B U0) -> ((euclidean__axioms.neq B U0) -> ((euclidean__axioms.Cong v U0 v U0) -> (euclidean__axioms.Col B A G))))))))))))))))))))) with (x := U).
----------------------------------------------------------intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
exact H37.

---------------------------------------------------------- exact H34.
---------------------------------------------------------- exact H18.
---------------------------------------------------------- exact H26.
---------------------------------------------------------- exact H90.
---------------------------------------------------------- exact H91.
---------------------------------------------------------- exact H36.
---------------------------------------------------------- exact H48.
---------------------------------------------------------- exact H49.
---------------------------------------------------------- exact H50.
---------------------------------------------------------- exact H51.
---------------------------------------------------------- exact H52.
---------------------------------------------------------- exact H55.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- exact H57.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- exact H95.
---------------------------------------------------------- exact H94.
---------------------------------------------------------- exact H93.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- exact H97.

--------------------------------------------------------- exact H67.
--------------------------------------------------------- exact H20.
--------------------------------------------------------- exact H28.
--------------------------------------------------------- exact H30.
--------------------------------------------------------- exact H35.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- exact H69.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- exact H71.
--------------------------------------------------------- exact H72.
--------------------------------------------------------- exact H73.
--------------------------------------------------------- exact H74.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B A) as H89.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H89.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A G H88).
---------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H94.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H90.
---------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict B A G H9).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H91.
----------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B G H90).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H92.
------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col B C A).
-------------------------------------------------------------intro H92.
apply (@euclidean__tactics.Col__nCol__False B C A H92).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G B C A H87 H89 H91).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H93.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H93.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C A H92).
-------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H98.
------------------------------------------------------------- apply (@H46).
--------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col B A J).
---------------------------------------------------------------intro H94.
apply (@euclidean__tactics.Col__nCol__False A B C H31 H93).


- exact H0.
Qed.
