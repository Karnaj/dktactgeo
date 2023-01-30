Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angleordertransitive.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__crossbar.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__ray1.
Require Export lemma__ray2.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Require Export proposition__05.
Require Export proposition__16.
Require Export proposition__19.
Definition proposition__24 : forall A B C D E F, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D E F) -> ((euclidean__axioms.Cong A B D E) -> ((euclidean__axioms.Cong A C D F) -> ((euclidean__defs.LtA E D F B A C) -> (euclidean__defs.Lt E F B C))))).
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
assert (euclidean__axioms.nCol A B C) as H4 by exact H.
assert (* Cut *) (~(A = B)) as H5.
- intro H5.
assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
-- left.
exact H5.
-- apply (@euclidean__tactics.Col__nCol__False A B C H4 H6).
- assert (* Cut *) (~(A = C)) as H6.
-- intro H6.
assert (* Cut *) (euclidean__axioms.Col A B C) as H7.
--- right.
left.
exact H6.
--- apply (@euclidean__tactics.Col__nCol__False A B C H4 H7).
-- assert (* Cut *) (euclidean__axioms.neq C A) as H7.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A C H6).
--- assert (* Cut *) (~(B = C)) as H8.
---- intro H8.
assert (* Cut *) (euclidean__axioms.Col A B C) as H9.
----- right.
right.
left.
exact H8.
----- apply (@euclidean__tactics.Col__nCol__False A B C H4 H9).
---- assert (* Cut *) (euclidean__axioms.neq C B) as H9.
----- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H8).
----- assert (* Cut *) (exists P Q T, (euclidean__axioms.BetS P T Q) /\ ((euclidean__defs.Out A B P) /\ ((euclidean__defs.Out A C Q) /\ (euclidean__defs.CongA E D F B A T)))) as H10.
------ assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ (euclidean__defs.CongA E D F B A X)))) as H10 by exact H3.
assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out A B U) /\ ((euclidean__defs.Out A C V) /\ (euclidean__defs.CongA E D F B A X)))) as __TmpHyp by exact H10.
destruct __TmpHyp as [x H11].
destruct H11 as [x0 H12].
destruct H12 as [x1 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exists x.
exists x1.
exists x0.
split.
------- exact H14.
------- split.
-------- exact H16.
-------- split.
--------- exact H18.
--------- exact H19.
------ destruct H10 as [P H11].
destruct H11 as [Q H12].
destruct H12 as [T H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
assert (* Cut *) (euclidean__axioms.nCol B A T) as H20.
------- apply (@euclidean__tactics.nCol__notCol B A T).
--------apply (@euclidean__tactics.nCol__not__Col B A T).
---------apply (@lemma__equalanglesNC.lemma__equalanglesNC E D F B A T H19).


------- assert (* Cut *) (~(A = T)) as H21.
-------- intro H21.
assert (* Cut *) (euclidean__axioms.Col B A T) as H22.
--------- right.
right.
left.
exact H21.
--------- apply (@euclidean__tactics.Col__nCol__False B A T H20 H22).
-------- assert (* Cut *) (~(A = C)) as H22.
--------- intro H22.
assert (* Cut *) (euclidean__axioms.Col A B C) as H23.
---------- right.
left.
exact H22.
---------- apply (@H6 H22).
--------- assert (* Cut *) (exists H23, (euclidean__defs.Out A T H23) /\ (euclidean__axioms.Cong A H23 A C)) as H23.
---------- apply (@lemma__layoff.lemma__layoff A T A C H21 H22).
---------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
assert (* Cut *) (euclidean__axioms.Cong A H24 D F) as H28.
----------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A H24 A C D F H27 H2).
----------- assert (* Cut *) (~(euclidean__axioms.Col H24 A B)) as H29.
------------ intro H29.
assert (* Cut *) (euclidean__axioms.Col A T H24) as H30.
------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A T H24 H26).
------------- assert (* Cut *) (euclidean__axioms.Col H24 A T) as H31.
-------------- assert (* Cut *) ((euclidean__axioms.Col T A H24) /\ ((euclidean__axioms.Col T H24 A) /\ ((euclidean__axioms.Col H24 A T) /\ ((euclidean__axioms.Col A H24 T) /\ (euclidean__axioms.Col H24 T A))))) as H31.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A T H24 H30).
--------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H36.
-------------- assert (* Cut *) (euclidean__axioms.neq A H24) as H32.
--------------- apply (@lemma__raystrict.lemma__raystrict A T H24 H26).
--------------- assert (* Cut *) (euclidean__axioms.neq H24 A) as H33.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A H24 H32).
---------------- assert (* Cut *) (euclidean__axioms.Col A B T) as H34.
----------------- apply (@euclidean__tactics.not__nCol__Col A B T).
------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False A B T H34).
-------------------apply (@lemma__collinear4.lemma__collinear4 H24 A B T H29 H31 H33).


----------------- assert (* Cut *) (euclidean__axioms.Col B A T) as H35.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A T) /\ ((euclidean__axioms.Col B T A) /\ ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col A T B) /\ (euclidean__axioms.Col T B A))))) as H35.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A B T H34).
------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H36.
------------------ apply (@euclidean__tactics.Col__nCol__False B A T H20 H35).
------------ assert (* Cut *) (~(H24 = B)) as H30.
------------- intro H30.
assert (* Cut *) (euclidean__axioms.Col H24 A B) as H31.
-------------- right.
left.
exact H30.
-------------- apply (@H29 H31).
------------- assert (* Cut *) (B = B) as H31.
-------------- apply (@logic.eq__refl Point B).
-------------- assert (* Cut *) (euclidean__defs.Out A B B) as H32.
--------------- apply (@lemma__ray4.lemma__ray4 A B B).
----------------right.
left.
exact H31.

---------------- exact H5.
--------------- assert (* Cut *) (euclidean__defs.CongA E D F B A H24) as H33.
---------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper E D F B A T B H24 H19 H32 H26).
---------------- assert (* Cut *) (euclidean__defs.CongA B A H24 E D F) as H34.
----------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric E D F B A H24 H33).
----------------- assert (* Cut *) (euclidean__defs.CongA H24 A B F D E) as H35.
------------------ apply (@lemma__equalanglesflip.lemma__equalanglesflip B A H24 E D F H34).
------------------ assert (* Cut *) ((euclidean__axioms.Cong H24 B F E) /\ ((euclidean__defs.CongA A H24 B D F E) /\ (euclidean__defs.CongA A B H24 D E F))) as H36.
------------------- apply (@proposition__04.proposition__04 A H24 B D F E H28 H1 H35).
------------------- assert (* Cut *) (euclidean__defs.Out A Q C) as H37.
-------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
apply (@lemma__ray5.lemma__ray5 A C Q H18).
-------------------- assert (* Cut *) (euclidean__defs.Out A P B) as H38.
--------------------- destruct H36 as [H38 H39].
destruct H39 as [H40 H41].
apply (@lemma__ray5.lemma__ray5 A B P H16).
--------------------- assert (* Cut *) (euclidean__axioms.Col A Q C) as H39.
---------------------- destruct H36 as [H39 H40].
destruct H40 as [H41 H42].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A Q C H37).
---------------------- assert (* Cut *) (euclidean__axioms.Col A P B) as H40.
----------------------- destruct H36 as [H40 H41].
destruct H41 as [H42 H43].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A P B H38).
----------------------- assert (* Cut *) (~(euclidean__axioms.Col Q A P)) as H41.
------------------------ intro H41.
assert (* Cut *) (euclidean__axioms.Col A P Q) as H42.
------------------------- destruct H36 as [H42 H43].
destruct H43 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q))))) as H46.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q A P H41).
-------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H49.
------------------------- assert (* Cut *) (euclidean__axioms.Col Q A C) as H43.
-------------------------- destruct H36 as [H43 H44].
destruct H44 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.Col Q A C) /\ ((euclidean__axioms.Col Q C A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A))))) as H47.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder A Q C H39).
--------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
-------------------------- assert (* Cut *) (euclidean__axioms.Col Q A P) as H44.
--------------------------- destruct H36 as [H44 H45].
destruct H45 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.Col A Q C) /\ ((euclidean__axioms.Col A C Q) /\ ((euclidean__axioms.Col C Q A) /\ ((euclidean__axioms.Col Q C A) /\ (euclidean__axioms.Col C A Q))))) as H48.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q A C H43).
---------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H41.
--------------------------- assert (* Cut *) (euclidean__axioms.neq A Q) as H45.
---------------------------- destruct H36 as [H45 H46].
destruct H46 as [H47 H48].
apply (@lemma__ray2.lemma__ray2 A Q C H37).
---------------------------- assert (* Cut *) (euclidean__axioms.neq Q A) as H46.
----------------------------- destruct H36 as [H46 H47].
destruct H47 as [H48 H49].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A Q H45).
----------------------------- assert (* Cut *) (euclidean__axioms.Col A C P) as H47.
------------------------------ destruct H36 as [H47 H48].
destruct H48 as [H49 H50].
apply (@euclidean__tactics.not__nCol__Col A C P).
-------------------------------intro H51.
apply (@euclidean__tactics.Col__nCol__False A C P H51).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 Q A C P H43 H44 H46).


------------------------------ assert (* Cut *) (euclidean__axioms.Col P A B) as H48.
------------------------------- destruct H36 as [H48 H49].
destruct H49 as [H50 H51].
assert (* Cut *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col B P A))))) as H52.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A P B H40).
-------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H53.
------------------------------- assert (* Cut *) (euclidean__axioms.Col P A C) as H49.
-------------------------------- destruct H36 as [H49 H50].
destruct H50 as [H51 H52].
assert (* Cut *) ((euclidean__axioms.Col C A P) /\ ((euclidean__axioms.Col C P A) /\ ((euclidean__axioms.Col P A C) /\ ((euclidean__axioms.Col A P C) /\ (euclidean__axioms.Col P C A))))) as H53.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C P H47).
--------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H58.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq A P) as H50.
--------------------------------- destruct H36 as [H50 H51].
destruct H51 as [H52 H53].
apply (@lemma__raystrict.lemma__raystrict A B P H16).
--------------------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H51.
---------------------------------- destruct H36 as [H51 H52].
destruct H52 as [H53 H54].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A P H50).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H52.
----------------------------------- destruct H36 as [H52 H53].
destruct H53 as [H54 H55].
apply (@euclidean__tactics.not__nCol__Col A B C).
------------------------------------intro H56.
apply (@euclidean__tactics.Col__nCol__False A B C H56).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 P A B C H48 H49 H51).


----------------------------------- apply (@H29).
------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-------------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False A B C H4 H52).


------------------------ assert (* Cut *) (euclidean__axioms.Triangle Q A P) as H42.
------------------------- apply (@euclidean__tactics.nCol__notCol Q A P H41).
------------------------- assert (* Cut *) (euclidean__axioms.BetS Q T P) as H43.
-------------------------- destruct H36 as [H43 H44].
destruct H44 as [H45 H46].
apply (@euclidean__axioms.axiom__betweennesssymmetry P T Q H14).
-------------------------- assert (* Cut *) (exists J, (euclidean__defs.Out A T J) /\ (euclidean__axioms.BetS C J B)) as H44.
--------------------------- destruct H36 as [H44 H45].
destruct H45 as [H46 H47].
apply (@lemma__crossbar.lemma__crossbar Q A P T C B H42 H43 H37 H38).
--------------------------- destruct H44 as [J H45].
destruct H45 as [H46 H47].
destruct H36 as [H48 H49].
destruct H49 as [H50 H51].
assert (* Cut *) (euclidean__defs.Out A J H24) as H52.
---------------------------- apply (@lemma__ray3.lemma__ray3 A T J H24 H46 H26).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A H24) as H53.
----------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A H24 C H27).
----------------------------- assert (* Cut *) (~(euclidean__axioms.Col A C H24)) as H54.
------------------------------ intro H54.
assert (* Cut *) (euclidean__axioms.Col H24 A C) as H55.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A H24) /\ ((euclidean__axioms.Col C H24 A) /\ ((euclidean__axioms.Col H24 A C) /\ ((euclidean__axioms.Col A H24 C) /\ (euclidean__axioms.Col H24 C A))))) as H55.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C H24 H54).
-------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
------------------------------- assert (* Cut *) (euclidean__axioms.neq A H24) as H56.
-------------------------------- apply (@lemma__raystrict.lemma__raystrict A J H24 H52).
-------------------------------- assert (* Cut *) (euclidean__axioms.neq H24 A) as H57.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A H24 H56).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col A J H24) as H58.
---------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A J H24 H52).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col H24 A J) as H59.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col J A H24) /\ ((euclidean__axioms.Col J H24 A) /\ ((euclidean__axioms.Col H24 A J) /\ ((euclidean__axioms.Col A H24 J) /\ (euclidean__axioms.Col H24 J A))))) as H59.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A J H24 H58).
------------------------------------ destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H64.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col A C J) as H60.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col A C J).
-------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False A C J H60).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 H24 A C J H55 H59 H57).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col C J B) as H61.
------------------------------------- right.
right.
right.
right.
left.
exact H47.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col C J A) as H62.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A J) /\ ((euclidean__axioms.Col C J A) /\ ((euclidean__axioms.Col J A C) /\ ((euclidean__axioms.Col A J C) /\ (euclidean__axioms.Col J C A))))) as H62.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C J H60).
--------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H65.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq C J) as H63.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J B) /\ ((euclidean__axioms.neq C J) /\ (euclidean__axioms.neq C B))) as H63.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C J B H47).
---------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H66.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col J B A) as H64.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col J B A).
-----------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False J B A H64).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C J B A H61 H62 H63).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A T J) as H65.
----------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A T J H46).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col J A T) as H66.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col T A J) /\ ((euclidean__axioms.Col T J A) /\ ((euclidean__axioms.Col J A T) /\ ((euclidean__axioms.Col A J T) /\ (euclidean__axioms.Col J T A))))) as H66.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A T J H65).
------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H71.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col J A B) as H67.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B J A) /\ ((euclidean__axioms.Col B A J) /\ ((euclidean__axioms.Col A J B) /\ ((euclidean__axioms.Col J A B) /\ (euclidean__axioms.Col A B J))))) as H67.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder J B A H64).
-------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H74.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A J) as H68.
-------------------------------------------- apply (@lemma__raystrict.lemma__raystrict A T J H46).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J A) as H69.
--------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A J H68).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A T B) as H70.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A T B).
-----------------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False A T B H70).
------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 J A T B H66 H67 H69).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A T) as H71.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B A T) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col B T A))))) as H71.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A T B H70).
------------------------------------------------ destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H76.
----------------------------------------------- apply (@H29).
------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False B A T H20 H71).


------------------------------ assert (* Cut *) (euclidean__axioms.Triangle A C H24) as H55.
------------------------------- apply (@euclidean__tactics.nCol__notCol A C H24 H54).
------------------------------- assert (* Cut *) (euclidean__defs.isosceles A C H24) as H56.
-------------------------------- split.
--------------------------------- exact H55.
--------------------------------- exact H53.
-------------------------------- assert (* Cut *) (euclidean__defs.CongA A C H24 A H24 C) as H57.
--------------------------------- apply (@proposition__05.proposition__05 A C H24 H56).
--------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A H24 J) \/ ((J = H24) \/ (euclidean__axioms.BetS A J H24))) as H58.
---------------------------------- apply (@lemma__ray1.lemma__ray1 A J H24 H52).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B C B) as H59.
----------------------------------- assert ((euclidean__axioms.BetS A H24 J) \/ ((J = H24) \/ (euclidean__axioms.BetS A J H24))) as H59 by exact H58.
assert ((euclidean__axioms.BetS A H24 J) \/ ((J = H24) \/ (euclidean__axioms.BetS A J H24))) as __TmpHyp by exact H59.
destruct __TmpHyp as [H60|H60].
------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col C J H24)) as H61.
------------------------------------- intro H61.
assert (* Cut *) (euclidean__axioms.Col A H24 J) as H62.
-------------------------------------- right.
right.
right.
right.
left.
exact H60.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H24 A) as H63.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 A J) /\ ((euclidean__axioms.Col H24 J A) /\ ((euclidean__axioms.Col J A H24) /\ ((euclidean__axioms.Col A J H24) /\ (euclidean__axioms.Col J H24 A))))) as H63.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H24 J H62).
---------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H71.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H24 C) as H64.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J C H24) /\ ((euclidean__axioms.Col J H24 C) /\ ((euclidean__axioms.Col H24 C J) /\ ((euclidean__axioms.Col C H24 J) /\ (euclidean__axioms.Col H24 J C))))) as H64.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C J H24 H61).
----------------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H67.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq H24 J) as H65.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H24 J) /\ ((euclidean__axioms.neq A H24) /\ (euclidean__axioms.neq A J))) as H65.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A H24 J H60).
------------------------------------------ destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq J H24) as H66.
------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H24 J H65).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H24 A C) as H67.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H24 A C).
--------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False H24 A C H67).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 J H24 A C H63 H64 H66).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C H24) as H68.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A H24 C) /\ ((euclidean__axioms.Col A C H24) /\ ((euclidean__axioms.Col C H24 A) /\ ((euclidean__axioms.Col H24 C A) /\ (euclidean__axioms.Col C A H24))))) as H68.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H24 A C H67).
--------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H71.
-------------------------------------------- apply (@H29).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
----------------------------------------------intro H69.
apply (@H54 H68).


------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle C J H24) as H62.
-------------------------------------- apply (@euclidean__tactics.nCol__notCol C J H24 H61).
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS J H24 A) as H63.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A H24 J H60).
--------------------------------------- assert (* Cut *) (euclidean__defs.LtA J C H24 C H24 A) as H64.
---------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H64.
----------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
------------------------------------------ apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
------------------------------------------ destruct __1 as [__1 __2].
exact __1.
----------------------------------------- apply (@H64 C J H24 A H62 H63).
---------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H24 C J)) as H65.
----------------------------------------- intro H65.
assert (* Cut *) (euclidean__axioms.Col C J H24) as H66.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C H24 J) /\ ((euclidean__axioms.Col C J H24) /\ ((euclidean__axioms.Col J H24 C) /\ ((euclidean__axioms.Col H24 J C) /\ (euclidean__axioms.Col J C H24))))) as H66.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H24 C J H65).
------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H69.
------------------------------------------ apply (@H29).
-------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
--------------------------------------------intro H67.
apply (@H61 H66).


----------------------------------------- assert (* Cut *) (euclidean__defs.CongA H24 C J J C H24) as H66.
------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA H24 C J).
-------------------------------------------apply (@euclidean__tactics.nCol__notCol H24 C J H65).

------------------------------------------ assert (* Cut *) (euclidean__defs.LtA H24 C J C H24 A) as H67.
------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 J C H24 C H24 A H24 C J H64 H66).
------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A H24 C)) as H68.
-------------------------------------------- intro H68.
assert (* Cut *) (euclidean__axioms.Col A C H24) as H69.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 A C) /\ ((euclidean__axioms.Col H24 C A) /\ ((euclidean__axioms.Col C A H24) /\ ((euclidean__axioms.Col A C H24) /\ (euclidean__axioms.Col C H24 A))))) as H69.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H24 C H68).
---------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H76.
--------------------------------------------- apply (@H29).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------intro H70.
apply (@H54 H69).


-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H24 C C H24 A) as H69.
--------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A H24 C).
----------------------------------------------apply (@euclidean__tactics.nCol__notCol A H24 C H68).

--------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H24 C J A H24 C) as H70.
---------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence H24 C J C H24 A A H24 C H67 H69).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out H24 B B) as H71.
----------------------------------------------- apply (@lemma__ray4.lemma__ray4 H24 B B).
------------------------------------------------right.
left.
exact H31.

------------------------------------------------ exact H30.
----------------------------------------------- assert (* Cut *) (C = C) as H72.
------------------------------------------------ apply (@logic.eq__refl Point C).
------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col C H24 J)) as H73.
------------------------------------------------- intro H73.
assert (* Cut *) (euclidean__axioms.Col C J H24) as H74.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 C J) /\ ((euclidean__axioms.Col H24 J C) /\ ((euclidean__axioms.Col J C H24) /\ ((euclidean__axioms.Col C J H24) /\ (euclidean__axioms.Col J H24 C))))) as H74.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C H24 J H73).
--------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H81.
-------------------------------------------------- apply (@H29).
---------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
----------------------------------------------------intro H75.
apply (@H61 H74).


------------------------------------------------- assert (* Cut *) (~(C = H24)) as H74.
-------------------------------------------------- intro H74.
assert (* Cut *) (euclidean__axioms.Col C H24 J) as H75.
--------------------------------------------------- left.
exact H74.
--------------------------------------------------- apply (@H29).
----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------------intro H76.
apply (@H73 H75).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H24 C) as H75.
--------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C H24 H74).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H24 C C) as H76.
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 H24 C C).
-----------------------------------------------------right.
left.
exact H72.

----------------------------------------------------- exact H75.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C H24 J C H24 J) as H77.
----------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive C H24 J).
------------------------------------------------------apply (@euclidean__tactics.nCol__notCol C H24 J H73).

----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C J) as H78.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 J) /\ ((euclidean__axioms.neq C J) /\ ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 J) /\ (euclidean__axioms.neq C J)))))) as H78.
------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct C H24 J C H24 J H77).
------------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H88.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C H24) as H79.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 J) /\ ((euclidean__axioms.neq C J) /\ ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 J) /\ (euclidean__axioms.neq C J)))))) as H79.
-------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct C H24 J C H24 J H77).
-------------------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H86.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA C H24 J C H24 B) as H80.
-------------------------------------------------------- exists C.
exists J.
exists B.
split.
--------------------------------------------------------- exact H47.
--------------------------------------------------------- split.
---------------------------------------------------------- exact H76.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H71.
----------------------------------------------------------- exact H77.
-------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C A H24)) as H81.
--------------------------------------------------------- intro H81.
assert (* Cut *) (euclidean__axioms.Col A C H24) as H82.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C H24) /\ ((euclidean__axioms.Col A H24 C) /\ ((euclidean__axioms.Col H24 C A) /\ ((euclidean__axioms.Col C H24 A) /\ (euclidean__axioms.Col H24 A C))))) as H82.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C A H24 H81).
----------------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H83.
---------------------------------------------------------- apply (@H29).
-----------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
------------------------------------------------------------intro H83.
apply (@H54 H82).


--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle C A H24) as H82.
---------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol C A H24 H81).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A C H24 C H24 J) as H83.
----------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H83.
------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
------------------------------------------------------------- apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
------------------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
------------------------------------------------------------ apply (@H83 C A H24 J H82 H60).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H24 C J A C H24) as H84.
------------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence H24 C J A H24 C A C H24 H70 H57).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA H24 C J C H24 J) as H85.
------------------------------------------------------------- apply (@lemma__angleordertransitive.lemma__angleordertransitive H24 C J A C H24 C H24 J H84 H83).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H24 C J C H24 B) as H86.
-------------------------------------------------------------- apply (@lemma__angleordertransitive.lemma__angleordertransitive H24 C J C H24 J C H24 B H85 H80).
-------------------------------------------------------------- assert (* Cut *) (H24 = H24) as H87.
--------------------------------------------------------------- apply (@logic.eq__refl Point H24).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C H24 H24) as H88.
---------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C H24 H24).
-----------------------------------------------------------------right.
left.
exact H87.

----------------------------------------------------------------- exact H79.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C J B) as H89.
----------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C J B).
------------------------------------------------------------------right.
right.
exact H47.

------------------------------------------------------------------ exact H78.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H24 C J H24 C J) as H90.
------------------------------------------------------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive H24 C J).
-------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol H24 C J H65).

------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H24 C J H24 C B) as H91.
------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper H24 C J H24 C J H24 B H90 H88 H89).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H24 C B H24 C J) as H92.
-------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric H24 C J H24 C B H91).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H24 C B C H24 B) as H93.
--------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 H24 C J C H24 B H24 C B H86 H92).
--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B H24 C)) as H94.
---------------------------------------------------------------------- intro H94.
assert (* Cut *) (euclidean__axioms.Col C J B) as H95.
----------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H47.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C H24) as H96.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H24 B C) /\ ((euclidean__axioms.Col H24 C B) /\ ((euclidean__axioms.Col C B H24) /\ ((euclidean__axioms.Col B C H24) /\ (euclidean__axioms.Col C H24 B))))) as H96.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B H24 C H94).
------------------------------------------------------------------------- destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H103.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C J) as H97.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J C B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B C J) /\ ((euclidean__axioms.Col C B J) /\ (euclidean__axioms.Col B J C))))) as H97.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C J B H95).
-------------------------------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H102.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H98.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H24 A) /\ ((euclidean__axioms.neq J H24) /\ (euclidean__axioms.neq J A))) as H98.
--------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal J H24 A H63).
--------------------------------------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H9.
-------------------------------------------------------------------------- assert (euclidean__axioms.neq B C) as H99 by exact H8.
assert (* Cut *) (euclidean__axioms.Col C H24 J) as H100.
--------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C H24 J).
----------------------------------------------------------------------------intro H100.
apply (@H61).
-----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 B C J H24 H97 H96 H99).


--------------------------------------------------------------------------- apply (@H29).
----------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------------------------------------intro H101.
apply (@H73 H100).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B H24 C) as H95.
----------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol B H24 C H94).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B H24 C C H24 B) as H96.
------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B H24 C H95).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA H24 C B B H24 C) as H97.
------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence H24 C B C H24 B B H24 C H93 H96).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt B H24 B C) as H98.
-------------------------------------------------------------------------- apply (@proposition__19.proposition__19 B H24 C H95 H97).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B H24 H24 B) as H99.
--------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B H24).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B B C) as H100.
---------------------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 B H24 B C H24 B H98 H99).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C C B) as H101.
----------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B C).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B C B) as H102.
------------------------------------------------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence H24 B B C C B H100 H101).
------------------------------------------------------------------------------ exact H102.
------------------------------------ destruct H60 as [H61|H61].
------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H24 B) as H62.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point H24 (fun J0 => (euclidean__defs.Out A T J0) -> ((euclidean__axioms.BetS C J0 B) -> ((euclidean__defs.Out A J0 H24) -> (euclidean__axioms.BetS C H24 B))))) with (x := J).
---------------------------------------intro H62.
intro H63.
intro H64.
exact H63.

--------------------------------------- exact H61.
--------------------------------------- exact H46.
--------------------------------------- exact H47.
--------------------------------------- exact H52.
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B H24 C) as H63.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C H24 B H62).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B H24 H24 B) as H64.
---------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B H24).
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B B C) as H65.
----------------------------------------- exists H24.
split.
------------------------------------------ exact H63.
------------------------------------------ exact H64.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C C B) as H66.
------------------------------------------ apply (@euclidean__axioms.cn__equalityreverse B C).
------------------------------------------ assert (* Cut *) (euclidean__defs.Lt H24 B C B) as H67.
------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence H24 B B C C B H65 H66).
------------------------------------------- exact H67.
------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H24 J A) as H62.
-------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A J H24 H61).
-------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C J H24)) as H63.
--------------------------------------- intro H63.
assert (* Cut *) (euclidean__axioms.Col A H24 J) as H64.
---------------------------------------- right.
right.
right.
right.
right.
exact H61.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H24 A) as H65.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 A J) /\ ((euclidean__axioms.Col H24 J A) /\ ((euclidean__axioms.Col J A H24) /\ ((euclidean__axioms.Col A J H24) /\ (euclidean__axioms.Col J H24 A))))) as H65.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A H24 J H64).
------------------------------------------ destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H73.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col J H24 C) as H66.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col J C H24) /\ ((euclidean__axioms.Col J H24 C) /\ ((euclidean__axioms.Col H24 C J) /\ ((euclidean__axioms.Col C H24 J) /\ (euclidean__axioms.Col H24 J C))))) as H66.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C J H24 H63).
------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H69.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H24 J) as H67.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J A) /\ ((euclidean__axioms.neq H24 J) /\ (euclidean__axioms.neq H24 A))) as H67.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H24 J A H62).
-------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H70.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J H24) as H68.
-------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H24 J H67).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H24 A C) as H69.
--------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H24 A C).
----------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False H24 A C H69).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 J H24 A C H65 H66 H68).


--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C H24) as H70.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A H24 C) /\ ((euclidean__axioms.Col A C H24) /\ ((euclidean__axioms.Col C H24 A) /\ ((euclidean__axioms.Col H24 C A) /\ (euclidean__axioms.Col C A H24))))) as H70.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H24 A C H69).
----------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H73.
---------------------------------------------- apply (@H29).
-----------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
------------------------------------------------intro H71.
apply (@H54 H70).


--------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H24 C B)) as H64.
---------------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.Col C J B) as H65.
----------------------------------------- right.
right.
right.
right.
left.
exact H47.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C J) as H66.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col J C B) /\ ((euclidean__axioms.Col J B C) /\ ((euclidean__axioms.Col B C J) /\ ((euclidean__axioms.Col C B J) /\ (euclidean__axioms.Col B J C))))) as H66.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C J B H65).
------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H71.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C H24) as H67.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H24 B) /\ ((euclidean__axioms.Col C B H24) /\ ((euclidean__axioms.Col B H24 C) /\ ((euclidean__axioms.Col H24 B C) /\ (euclidean__axioms.Col B C H24))))) as H67.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H24 C B H64).
-------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H75.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H68.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J A) /\ ((euclidean__axioms.neq H24 J) /\ (euclidean__axioms.neq H24 A))) as H68.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H24 J A H62).
--------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H9.
-------------------------------------------- assert (euclidean__axioms.neq B C) as H69 by exact H8.
assert (* Cut *) (euclidean__axioms.Col C H24 J) as H70.
--------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C H24 J).
----------------------------------------------intro H70.
apply (@H63).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 B C J H24 H66 H67 H69).


--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C J H24) as H71.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 C J) /\ ((euclidean__axioms.Col H24 J C) /\ ((euclidean__axioms.Col J C H24) /\ ((euclidean__axioms.Col C J H24) /\ (euclidean__axioms.Col J H24 C))))) as H71.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C H24 J H70).
----------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
---------------------------------------------- apply (@H29).
-----------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
------------------------------------------------intro H72.
apply (@H63 H71).


---------------------------------------- assert (* Cut *) (H24 = H24) as H65.
----------------------------------------- apply (@logic.eq__refl Point H24).
----------------------------------------- assert (* Cut *) (A = A) as H66.
------------------------------------------ apply (@logic.eq__refl Point A).
------------------------------------------ assert (* Cut *) (~(C = H24)) as H67.
------------------------------------------- intro H67.
assert (* Cut *) (euclidean__axioms.Col C H24 B) as H68.
-------------------------------------------- left.
exact H67.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H24 C B) as H69.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 C B) /\ ((euclidean__axioms.Col H24 B C) /\ ((euclidean__axioms.Col B C H24) /\ ((euclidean__axioms.Col C B H24) /\ (euclidean__axioms.Col B H24 C))))) as H69.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C H24 B H68).
---------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H70.
--------------------------------------------- apply (@H29).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------intro H70.
apply (@H64 H69).


------------------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H68.
-------------------------------------------- apply (@lemma__ray4.lemma__ray4 C A A).
---------------------------------------------right.
left.
exact H66.

--------------------------------------------- exact H7.
-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H24 C B H24 C B) as H69.
--------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive H24 C B).
----------------------------------------------apply (@euclidean__tactics.nCol__notCol H24 C B H64).

--------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B J) as H70.
---------------------------------------------- apply (@lemma__ray4.lemma__ray4 C B J).
-----------------------------------------------left.
exact H47.

----------------------------------------------- exact H9.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out C H24 H24) as H71.
----------------------------------------------- apply (@lemma__ray4.lemma__ray4 C H24 H24).
------------------------------------------------right.
left.
exact H65.

------------------------------------------------ exact H67.
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H24 C B H24 C J) as H72.
------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper H24 C B H24 C B H24 J H69 H71 H70).
------------------------------------------------ assert (euclidean__axioms.BetS H24 J A) as H73 by exact H62.
assert (* Cut *) (euclidean__defs.LtA H24 C B H24 C A) as H74.
------------------------------------------------- exists H24.
exists J.
exists A.
split.
-------------------------------------------------- exact H73.
-------------------------------------------------- split.
--------------------------------------------------- exact H71.
--------------------------------------------------- split.
---------------------------------------------------- exact H68.
---------------------------------------------------- exact H72.
------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C H24)) as H75.
-------------------------------------------------- intro H75.
assert (* Cut *) (euclidean__axioms.Col H24 C B) as H76.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B H24) /\ ((euclidean__axioms.Col C H24 B) /\ ((euclidean__axioms.Col H24 B C) /\ ((euclidean__axioms.Col B H24 C) /\ (euclidean__axioms.Col H24 C B))))) as H76.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C H24 H75).
---------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H84.
--------------------------------------------------- apply (@H29).
----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------------intro H77.
apply (@H64 H76).


-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C H24 H24 C B) as H76.
--------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C H24).
----------------------------------------------------apply (@euclidean__tactics.nCol__notCol B C H24 H75).

--------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C H24 H24 C A) as H77.
---------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 H24 C B H24 C A B C H24 H74 H76).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C H24 H24 C A) as H78.
----------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A C H24 H55).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C H24 A C H24) as H79.
------------------------------------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence B C H24 H24 C A A C H24 H77 H78).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A H24 C A C H24) as H80.
------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A C H24 A H24 C H57).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C H24 A H24 C) as H81.
-------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence B C H24 A C H24 A H24 C H79 H80).
-------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A H24 C)) as H82.
--------------------------------------------------------- intro H82.
assert (* Cut *) (euclidean__axioms.Col A C H24) as H83.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 A C) /\ ((euclidean__axioms.Col H24 C A) /\ ((euclidean__axioms.Col C A H24) /\ ((euclidean__axioms.Col A C H24) /\ (euclidean__axioms.Col C H24 A))))) as H83.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H24 C H82).
----------------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H90.
---------------------------------------------------------- apply (@H29).
-----------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
------------------------------------------------------------intro H84.
apply (@H54 H83).


--------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H24 C C H24 A) as H83.
---------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A H24 C).
-----------------------------------------------------------apply (@euclidean__tactics.nCol__notCol A H24 C H82).

---------------------------------------------------------- assert (* Cut *) (C = C) as H84.
----------------------------------------------------------- apply (@logic.eq__refl Point C).
----------------------------------------------------------- assert (B = B) as H85 by exact H31.
assert (* Cut *) (euclidean__axioms.neq H24 B) as H86.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A H24) /\ ((euclidean__axioms.neq H24 C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 A) /\ (euclidean__axioms.neq C A)))))) as H86.
------------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct A H24 C C H24 A H83).
------------------------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H30.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H24 C) as H87.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A H24) /\ ((euclidean__axioms.neq H24 C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 A) /\ (euclidean__axioms.neq C A)))))) as H87.
-------------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct A H24 C C H24 A H83).
-------------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H90.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H24 A) as H88.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A H24) /\ ((euclidean__axioms.neq H24 C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C H24) /\ ((euclidean__axioms.neq H24 A) /\ (euclidean__axioms.neq C A)))))) as H88.
--------------------------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct A H24 C C H24 A H83).
--------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H97.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H24 C C) as H89.
--------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 H24 C C).
----------------------------------------------------------------right.
left.
exact H84.

---------------------------------------------------------------- exact H87.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H24 B B) as H90.
---------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 H24 B B).
-----------------------------------------------------------------right.
left.
exact H85.

----------------------------------------------------------------- exact H86.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H24 A J) as H91.
----------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 H24 A J).
------------------------------------------------------------------left.
exact H73.

------------------------------------------------------------------ exact H88.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H24 C C H24 J) as H92.
------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper A H24 C C H24 A C J H83 H89 H91).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA A H24 C C H24 B) as H93.
------------------------------------------------------------------- exists C.
exists J.
exists B.
split.
-------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------- split.
---------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------- exact H92.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B H24 C)) as H94.
-------------------------------------------------------------------- intro H94.
assert (* Cut *) (euclidean__axioms.Col H24 C B) as H95.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H24 B C) /\ ((euclidean__axioms.Col H24 C B) /\ ((euclidean__axioms.Col C B H24) /\ ((euclidean__axioms.Col B C H24) /\ (euclidean__axioms.Col C H24 B))))) as H95.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B H24 C H94).
---------------------------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H98.
--------------------------------------------------------------------- apply (@H29).
----------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
-----------------------------------------------------------------------intro H96.
apply (@H64 H95).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B H24 C C H24 B) as H95.
--------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B H24 C).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol B H24 C H94).

--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA A H24 C B H24 C) as H96.
---------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence A H24 C C H24 B B H24 C H93 H95).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C H24 B H24 C) as H97.
----------------------------------------------------------------------- apply (@lemma__angleordertransitive.lemma__angleordertransitive B C H24 A H24 C B H24 C H81 H96).
----------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col H24 C B)) as H98.
------------------------------------------------------------------------ intro H98.
assert (* Cut *) (euclidean__axioms.Col B H24 C) as H99.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H24 B) /\ ((euclidean__axioms.Col C B H24) /\ ((euclidean__axioms.Col B H24 C) /\ ((euclidean__axioms.Col H24 B C) /\ (euclidean__axioms.Col B C H24))))) as H99.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H24 C B H98).
-------------------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H104.
------------------------------------------------------------------------- apply (@H29).
--------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col H24 A B).
---------------------------------------------------------------------------intro H100.
apply (@H64 H98).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H24 C B B C H24) as H99.
------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA H24 C B).
--------------------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol H24 C B H98).

------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA H24 C B B H24 C) as H100.
-------------------------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 B C H24 B H24 C H24 C B H97 H99).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B H24 C) as H101.
--------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol B H24 C H94).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt B H24 B C) as H102.
---------------------------------------------------------------------------- apply (@proposition__19.proposition__19 B H24 C H101 H100).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B H24 H24 B) as H103.
----------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B H24).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B B C) as H104.
------------------------------------------------------------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 B H24 B C H24 B H102 H103).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B C C B) as H105.
------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B C).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt H24 B C B) as H106.
-------------------------------------------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence H24 B B C C B H104 H105).
-------------------------------------------------------------------------------- exact H106.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E E F) as H60.
------------------------------------ apply (@euclidean__axioms.cn__equalityreverse F E).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong H24 B E F) as H61.
------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive H24 B F E E F H48 H60).
------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F C B) as H62.
-------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 H24 B C B E F H59 H61).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B B C) as H63.
--------------------------------------- apply (@euclidean__axioms.cn__equalityreverse C B).
--------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F B C) as H64.
---------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence E F C B B C H62 H63).
---------------------------------------- exact H64.
Qed.
