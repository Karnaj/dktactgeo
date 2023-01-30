Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__10__12.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__TGflip.
Require Export lemma__TGsymmetric.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__layoffunique.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export logic.
Require Export proposition__20.
Require Export proposition__22.
Definition lemma__Euclid4 : forall A B C a b c, (euclidean__defs.Per A B C) -> ((euclidean__defs.Per a b c) -> (euclidean__defs.CongA A B C a b c)).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
assert (exists D, (euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H1 by exact H.
destruct H1 as [D H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
assert (exists d, (euclidean__axioms.BetS a b d) /\ ((euclidean__axioms.Cong a b d b) /\ ((euclidean__axioms.Cong a c d c) /\ (euclidean__axioms.neq b c)))) as H9 by exact H0.
destruct H9 as [d H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
assert (* Cut *) (euclidean__axioms.neq a b) as H17.
- assert (* Cut *) ((euclidean__axioms.neq b d) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a d))) as H17.
-- apply (@lemma__betweennotequal.lemma__betweennotequal a b d H11).
-- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H20.
- assert (* Cut *) (euclidean__axioms.neq b a) as H18.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric a b H17).
-- assert (* Cut *) (euclidean__axioms.neq A B) as H19.
--- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H19.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A B D H3).
---- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H22.
--- assert (* Cut *) (euclidean__axioms.neq B A) as H20.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H19).
---- assert (* Cut *) (exists p, (euclidean__defs.Out b a p) /\ (euclidean__axioms.Cong b p B A)) as H21.
----- apply (@lemma__layoff.lemma__layoff b a B A H18 H20).
----- destruct H21 as [p H22].
destruct H22 as [H23 H24].
assert (* Cut *) (exists q, (euclidean__defs.Out b c q) /\ (euclidean__axioms.Cong b q B C)) as H25.
------ apply (@lemma__layoff.lemma__layoff b c B C H16 H8).
------ destruct H25 as [q H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__defs.Per a b q) as H29.
------- apply (@lemma__8__3.lemma__8__3 a b c q H0 H27).
------- assert (* Cut *) (euclidean__defs.Per q b a) as H30.
-------- apply (@lemma__8__2.lemma__8__2 a b q H29).
-------- assert (* Cut *) (euclidean__defs.Per q b p) as H31.
--------- apply (@lemma__8__3.lemma__8__3 q b a p H30 H23).
--------- assert (* Cut *) (euclidean__defs.Per p b q) as H32.
---------- apply (@lemma__8__2.lemma__8__2 q b p H31).
---------- assert (exists r, (euclidean__axioms.BetS p b r) /\ ((euclidean__axioms.Cong p b r b) /\ ((euclidean__axioms.Cong p q r q) /\ (euclidean__axioms.neq b q)))) as H33 by exact H32.
destruct H33 as [r H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
assert (* Cut *) (euclidean__axioms.Cong q p q r) as H41.
----------- assert (* Cut *) ((euclidean__axioms.Cong q p q r) /\ ((euclidean__axioms.Cong q p r q) /\ (euclidean__axioms.Cong p q q r))) as H41.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip p q r q H39).
------------ destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
----------- assert (* Cut *) (euclidean__axioms.nCol p b q) as H42.
------------ apply (@lemma__rightangleNC.lemma__rightangleNC p b q H32).
------------ assert (* Cut *) (~(euclidean__axioms.Col b q p)) as H43.
------------- intro H43.
assert (* Cut *) (euclidean__axioms.Col p b q) as H44.
-------------- assert (* Cut *) ((euclidean__axioms.Col q b p) /\ ((euclidean__axioms.Col q p b) /\ ((euclidean__axioms.Col p b q) /\ ((euclidean__axioms.Col b p q) /\ (euclidean__axioms.Col p q b))))) as H44.
--------------- apply (@lemma__collinearorder.lemma__collinearorder b q p H43).
--------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
-------------- apply (@euclidean__tactics.Col__nCol__False p b q H42 H44).
------------- assert (* Cut *) (~(euclidean__axioms.Col q p b)) as H44.
-------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col p b q) as H45.
--------------- assert (* Cut *) ((euclidean__axioms.Col p q b) /\ ((euclidean__axioms.Col p b q) /\ ((euclidean__axioms.Col b q p) /\ ((euclidean__axioms.Col q b p) /\ (euclidean__axioms.Col b p q))))) as H45.
---------------- apply (@lemma__collinearorder.lemma__collinearorder q p b H44).
---------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H48.
--------------- apply (@H43).
----------------apply (@euclidean__tactics.not__nCol__Col b q p).
-----------------intro H46.
apply (@euclidean__tactics.Col__nCol__False p b q H42 H45).


-------------- assert (euclidean__axioms.Triangle p b q) as H45 by exact H42.
assert (* Cut *) (euclidean__axioms.Triangle b q p) as H46.
--------------- apply (@euclidean__tactics.nCol__notCol b q p H43).
--------------- assert (* Cut *) (euclidean__axioms.Triangle q p b) as H47.
---------------- apply (@euclidean__tactics.nCol__notCol q p b H44).
---------------- assert (* Cut *) (euclidean__defs.TG b p p q b q) as H48.
----------------- apply (@proposition__20.proposition__20 p b q H45).
----------------- assert (* Cut *) (euclidean__defs.TG q b b p q p) as H49.
------------------ apply (@proposition__20.proposition__20 b q p H46).
------------------ assert (* Cut *) (euclidean__defs.TG p q q b p b) as H50.
------------------- apply (@proposition__20.proposition__20 q p b H47).
------------------- assert (* Cut *) (euclidean__defs.TG b q b p q p) as H51.
-------------------- assert (* Cut *) ((euclidean__defs.TG b q b p q p) /\ (euclidean__defs.TG q b b p p q)) as H51.
--------------------- apply (@lemma__TGflip.lemma__TGflip q b q b p p H49).
--------------------- destruct H51 as [H52 H53].
exact H52.
-------------------- assert (* Cut *) (euclidean__defs.TG b q b p p q) as H52.
--------------------- assert (* Cut *) ((euclidean__defs.TG q b b p q p) /\ (euclidean__defs.TG b q b p p q)) as H52.
---------------------- apply (@lemma__TGflip.lemma__TGflip b b q q p p H51).
---------------------- destruct H52 as [H53 H54].
exact H54.
--------------------- assert (* Cut *) (euclidean__defs.TG q b p q p b) as H53.
---------------------- apply (@lemma__TGsymmetric.lemma__TGsymmetric p q p q b b H50).
---------------------- assert (* Cut *) (euclidean__defs.TG b q p q p b) as H54.
----------------------- assert (* Cut *) ((euclidean__defs.TG b q p q p b) /\ (euclidean__defs.TG q b p q b p)) as H54.
------------------------ apply (@lemma__TGflip.lemma__TGflip q p p b q b H53).
------------------------ destruct H54 as [H55 H56].
exact H55.
----------------------- assert (* Cut *) (euclidean__defs.TG b q p q b p) as H55.
------------------------ assert (* Cut *) ((euclidean__defs.TG q b p q p b) /\ (euclidean__defs.TG b q p q b p)) as H55.
------------------------- apply (@lemma__TGflip.lemma__TGflip b p p q q b H54).
------------------------- destruct H55 as [H56 H57].
exact H57.
------------------------ assert (* Cut *) (euclidean__defs.TG b p p q q b) as H56.
------------------------- assert (* Cut *) ((euclidean__defs.TG p b p q b q) /\ (euclidean__defs.TG b p p q q b)) as H56.
-------------------------- apply (@lemma__TGflip.lemma__TGflip b p b p q q H48).
-------------------------- destruct H56 as [H57 H58].
exact H58.
------------------------- assert (* Cut *) (exists E F, (euclidean__axioms.Cong B E b p) /\ ((euclidean__axioms.Cong B F b q) /\ ((euclidean__axioms.Cong E F p q) /\ ((euclidean__defs.Out B A E) /\ (euclidean__axioms.Triangle B E F))))) as H57.
-------------------------- apply (@proposition__22.proposition__22 b b p A B q p q H52 H55 H48 H20).
-------------------------- destruct H57 as [E H58].
destruct H58 as [F H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
assert (* Cut *) (euclidean__axioms.BetS D B A) as H68.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A B D H3).
--------------------------- assert (* Cut *) (A = A) as H69.
---------------------------- apply (@logic.eq__refl Point A).
---------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H70.
----------------------------- apply (@lemma__ray4.lemma__ray4 B A A).
------------------------------right.
left.
exact H69.

------------------------------ exact H20.
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B E B A) as H71.
------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive B E b p B A H60 H24).
------------------------------ assert (* Cut *) (E = A) as H72.
------------------------------- apply (@lemma__layoffunique.lemma__layoffunique B A E A H66 H70 H71).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A b p) as H73.
-------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> (euclidean__axioms.Cong B A b p))))))) with (x := E).
---------------------------------intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
exact H73.

--------------------------------- exact H72.
--------------------------------- exact H60.
--------------------------------- exact H64.
--------------------------------- exact H66.
--------------------------------- exact H67.
--------------------------------- exact H71.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F p q) as H74.
--------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> (euclidean__axioms.Cong A F p q))))))) with (x := E).
----------------------------------intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
exact H75.

---------------------------------- exact H72.
---------------------------------- exact H60.
---------------------------------- exact H64.
---------------------------------- exact H66.
---------------------------------- exact H67.
---------------------------------- exact H71.
--------------------------------- assert (* Cut *) (~(p = b)) as H75.
---------------------------------- intro H75.
assert (* Cut *) (euclidean__axioms.Col p b q) as H76.
----------------------------------- left.
exact H75.
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol p b q) as H77.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point b (fun p0 => (euclidean__defs.Out b a p0) -> ((euclidean__axioms.Cong b p0 B A) -> ((euclidean__defs.Per q b p0) -> ((euclidean__defs.Per p0 b q) -> ((euclidean__axioms.BetS p0 b r) -> ((euclidean__axioms.Cong p0 b r b) -> ((euclidean__axioms.Cong p0 q r q) -> ((euclidean__axioms.Cong q p0 q r) -> ((euclidean__axioms.nCol p0 b q) -> ((~(euclidean__axioms.Col b q p0)) -> ((~(euclidean__axioms.Col q p0 b)) -> ((euclidean__axioms.Triangle p0 b q) -> ((euclidean__axioms.Triangle b q p0) -> ((euclidean__axioms.Triangle q p0 b) -> ((euclidean__defs.TG b p0 p0 q b q) -> ((euclidean__defs.TG q b b p0 q p0) -> ((euclidean__defs.TG p0 q q b p0 b) -> ((euclidean__defs.TG b q b p0 q p0) -> ((euclidean__defs.TG b q b p0 p0 q) -> ((euclidean__defs.TG q b p0 q p0 b) -> ((euclidean__defs.TG b q p0 q p0 b) -> ((euclidean__defs.TG b q p0 q b p0) -> ((euclidean__defs.TG b p0 p0 q q b) -> ((euclidean__axioms.Cong B E b p0) -> ((euclidean__axioms.Cong E F p0 q) -> ((euclidean__axioms.Cong B A b p0) -> ((euclidean__axioms.Cong A F p0 q) -> ((euclidean__axioms.Col p0 b q) -> (euclidean__axioms.nCol p0 b q)))))))))))))))))))))))))))))) with (x := p).
-------------------------------------intro H77.
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
apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b b) -> ((euclidean__axioms.Cong E0 F b q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> (euclidean__axioms.nCol b b q))))))) with (x := E).
--------------------------------------intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
exact H85.

-------------------------------------- exact H72.
-------------------------------------- exact H100.
-------------------------------------- exact H101.
-------------------------------------- exact H66.
-------------------------------------- exact H67.
-------------------------------------- exact H71.

------------------------------------- exact H75.
------------------------------------- exact H23.
------------------------------------- exact H24.
------------------------------------- exact H31.
------------------------------------- exact H32.
------------------------------------- exact H35.
------------------------------------- exact H37.
------------------------------------- exact H39.
------------------------------------- exact H41.
------------------------------------- exact H42.
------------------------------------- exact H43.
------------------------------------- exact H44.
------------------------------------- exact H45.
------------------------------------- exact H46.
------------------------------------- exact H47.
------------------------------------- exact H48.
------------------------------------- exact H49.
------------------------------------- exact H50.
------------------------------------- exact H51.
------------------------------------- exact H52.
------------------------------------- exact H53.
------------------------------------- exact H54.
------------------------------------- exact H55.
------------------------------------- exact H56.
------------------------------------- exact H60.
------------------------------------- exact H64.
------------------------------------- exact H73.
------------------------------------- exact H74.
------------------------------------- exact H76.
------------------------------------ apply (@H43).
-------------------------------------apply (@euclidean__tactics.not__nCol__Col b q p).
--------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False p b q H77 H76).


---------------------------------- assert (* Cut *) (euclidean__axioms.Cong r b p b) as H76.
----------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric r p b b H37).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong b r p b) as H77.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong b r b p) /\ ((euclidean__axioms.Cong b r p b) /\ (euclidean__axioms.Cong r b b p))) as H77.
------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip r b p b H76).
------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H80.
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong b p B E) as H78.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> (euclidean__axioms.Cong b p B E0))))))) with (x := E).
--------------------------------------intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
exact H24.

-------------------------------------- exact H72.
-------------------------------------- exact H60.
-------------------------------------- exact H64.
-------------------------------------- exact H66.
-------------------------------------- exact H67.
-------------------------------------- exact H71.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq b p) as H79.
-------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric p b H75).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H80.
--------------------------------------- apply (@euclidean__axioms.cn__equalityreverse B A).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p b b r) as H81.
---------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric p b r b H77).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p q r q) as H82.
----------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__axioms.Cong p q r q)))))))) with (x := E).
------------------------------------------intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
exact H39.

------------------------------------------ exact H72.
------------------------------------------ exact H60.
------------------------------------------ exact H64.
------------------------------------------ exact H66.
------------------------------------------ exact H67.
------------------------------------------ exact H71.
------------------------------------------ exact H78.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p b A B) as H83.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong p b A B) /\ (euclidean__axioms.Cong A B p b)) as H83.
------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse B A b p H73).
------------------------------------------- destruct H83 as [H84 H85].
exact H84.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong b r p b) as H84.
------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__axioms.Cong b r p b)))))))) with (x := E).
--------------------------------------------intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
exact H77.

-------------------------------------------- exact H72.
-------------------------------------------- exact H60.
-------------------------------------------- exact H64.
-------------------------------------------- exact H66.
-------------------------------------------- exact H67.
-------------------------------------------- exact H71.
-------------------------------------------- exact H78.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b r A B) as H85.
-------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive b r p b A B H84 H83).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B D) as H86.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A B D) /\ ((euclidean__axioms.Cong B A D B) /\ (euclidean__axioms.Cong A B B D))) as H86.
---------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B D B H5).
---------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H90.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b r B D) as H87.
---------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive b r A B B D H85 H86).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b q B F) as H88.
----------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B F q H62).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p q A F) as H89.
------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric p A F q H74).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong q r F D) as H90.
------------------------------------------------- apply (@euclidean__axioms.axiom__5__line p b r q A B D F H87 H89 H88 H35 H3 H83).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F r q) as H91.
-------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A F p q r q H74 H82).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F q r) as H92.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A q r) /\ ((euclidean__axioms.Cong F A r q) /\ (euclidean__axioms.Cong A F q r))) as H92.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A F r q H91).
---------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H96.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F F D) as H93.
---------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive A F q r F D H92 H90).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F D F) as H94.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A D F) /\ ((euclidean__axioms.Cong F A F D) /\ (euclidean__axioms.Cong A F D F))) as H94.
------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A F F D H93).
------------------------------------------------------ destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H98.
----------------------------------------------------- assert (euclidean__axioms.neq b q) as H95 by exact H40.
assert (* Cut *) (euclidean__axioms.Cong q b b q) as H96.
------------------------------------------------------ apply (@euclidean__axioms.cn__equalityreverse q b).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong q b B F) as H97.
------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive q b b q B F H96 H88).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H98.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__nocollapse b q B F H95 H88).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B F) as H99.
--------------------------------------------------------- exists D.
split.
---------------------------------------------------------- exact H3.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H5.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H94.
------------------------------------------------------------ exact H98.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b q B F) as H100.
---------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__axioms.Cong b q B F)))))))) with (x := E).
-----------------------------------------------------------intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
exact H88.

----------------------------------------------------------- exact H72.
----------------------------------------------------------- exact H60.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- exact H71.
----------------------------------------------------------- exact H78.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b q) as H101.
----------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B b q C H28).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B F) as H102.
------------------------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive B C b q B F H101 H100).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A C A F) as H103.
------------------------------------------------------------- apply (@lemma__10__12.lemma__10__12 A B C F H H99 H102).
------------------------------------------------------------- assert (* Cut *) (F = F) as H104.
-------------------------------------------------------------- apply (@logic.eq__refl Point F).
-------------------------------------------------------------- assert (* Cut *) (C = C) as H105.
--------------------------------------------------------------- apply (@logic.eq__refl Point C).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B F F) as H106.
---------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B F F).
-----------------------------------------------------------------right.
left.
exact H104.

----------------------------------------------------------------- exact H98.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H107.
----------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B C C).
------------------------------------------------------------------right.
left.
exact H105.

------------------------------------------------------------------ exact H8.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H108.
------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.Out B A A)))))))) with (x := E).
-------------------------------------------------------------------intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
exact H70.

------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- exact H60.
------------------------------------------------------------------- exact H64.
------------------------------------------------------------------- exact H66.
------------------------------------------------------------------- exact H67.
------------------------------------------------------------------- exact H71.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B A B A) as H109.
------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__axioms.Cong B A B A)))))))) with (x := E).
--------------------------------------------------------------------intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
exact H113.

-------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H110.
-------------------------------------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC A B C H).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B F) as H111.
--------------------------------------------------------------------- exists A.
exists C.
exists A.
exists F.
split.
---------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------- split.
----------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------- split.
------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H112.
---------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A B C H110).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B F) as H113.
----------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.CongA A B C A B F)))))))) with (x := E).
------------------------------------------------------------------------intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
exact H111.

------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------ exact H78.
----------------------------------------------------------------------- assert (* Cut *) (p = p) as H114.
------------------------------------------------------------------------ apply (@logic.eq__refl Point p).
------------------------------------------------------------------------ assert (* Cut *) (q = q) as H115.
------------------------------------------------------------------------- apply (@logic.eq__refl Point q).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out b p p) as H116.
-------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 b p p).
---------------------------------------------------------------------------right.
left.
exact H114.

--------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out b q q) as H117.
--------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 b q q).
----------------------------------------------------------------------------right.
left.
exact H115.

---------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B F F) as H118.
---------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.Out B F F)))))))) with (x := E).
-----------------------------------------------------------------------------intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
exact H106.

----------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H119.
----------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.Out B A A)))))))) with (x := E).
------------------------------------------------------------------------------intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
exact H108.

------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------ exact H78.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A b p) as H120.
------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__axioms.Cong B A b p)))))))) with (x := E).
-------------------------------------------------------------------------------intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
exact H73.

------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B A p b) as H121.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A B p b) /\ ((euclidean__axioms.Cong A B b p) /\ (euclidean__axioms.Cong B A p b))) as H121.
-------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B A b p H120).
-------------------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H125.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B F) as H122.
-------------------------------------------------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC A B F H99).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B F p b q) as H123.
--------------------------------------------------------------------------------- exists A.
exists F.
exists p.
exists q.
split.
---------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H62.
--------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C p b q) as H124.
---------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C A B F p b q H113 H123).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol a b c) as H125.
----------------------------------------------------------------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC a b c H0).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out b p p) as H126.
------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.Out b p p)))))))) with (x := E).
-------------------------------------------------------------------------------------intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
exact H116.

------------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------------- exact H66.
------------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------------- exact H71.
------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out b q q) as H127.
------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun E0 => (euclidean__axioms.Cong B E0 b p) -> ((euclidean__axioms.Cong E0 F p q) -> ((euclidean__defs.Out B A E0) -> ((euclidean__axioms.Triangle B E0 F) -> ((euclidean__axioms.Cong B E0 B A) -> ((euclidean__axioms.Cong b p B E0) -> (euclidean__defs.Out b q q)))))))) with (x := E).
--------------------------------------------------------------------------------------intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
exact H117.

-------------------------------------------------------------------------------------- exact H72.
-------------------------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b p b p) as H128.
-------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive b p).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong b q b q) as H129.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive b q).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p q p q) as H130.
---------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive p q).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA a b c p b q) as H131.
----------------------------------------------------------------------------------------- exists p.
exists q.
exists p.
exists q.
split.
------------------------------------------------------------------------------------------ exact H23.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H27.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------ exact H125.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA p b q a b c) as H132.
------------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric a b c p b q H131).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C a b c) as H133.
------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C p b q a b c H124 H132).
------------------------------------------------------------------------------------------- exact H133.
Qed.
