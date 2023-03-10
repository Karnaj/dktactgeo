Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__parallelcollinear2 : forall A B C c d, (euclidean__defs.TP A B c d) -> ((euclidean__axioms.BetS c C d) -> (euclidean__defs.TP A B C d)).
Proof.
intro A.
intro B.
intro C.
intro c.
intro d.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.BetS d C c) as H1.
- apply (@euclidean__axioms.axiom__betweennesssymmetry c C d H0).
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H2.
-- assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H2 by exact H.
assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as __TmpHyp by exact H2.
destruct __TmpHyp as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
split.
--- exact H3.
--- split.
---- exact H5.
---- split.
----- exact H7.
----- exact H8.
-- assert (* Cut *) (exists p q r, (euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))))) as H3.
--- assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))))) as H3 by exact H2.
assert ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))))) as __TmpHyp by exact H3.
destruct __TmpHyp as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [x H10].
destruct H10 as [x0 H11].
destruct H11 as [x1 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exists x0.
exists x.
exists x1.
split.
---- exact H13.
---- split.
----- exact H15.
----- split.
------ exact H17.
------ split.
------- exact H19.
------- split.
-------- exact H21.
-------- exact H22.
--- destruct H3 as [p H4].
destruct H4 as [q H5].
destruct H5 as [r H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H2 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) (euclidean__axioms.neq C d) as H23.
---- assert (* Cut *) ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.neq c C) /\ (euclidean__axioms.neq c d))) as H23.
----- apply (@lemma__betweennotequal.lemma__betweennotequal c C d H0).
----- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H24.
---- assert (* Cut *) (euclidean__axioms.BetS q p c) as H24.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry c p q H11).
----- assert (* Cut *) (euclidean__axioms.BetS q r d) as H25.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry d r q H13).
------ assert (euclidean__axioms.BetS d C c) as H26 by exact H1.
assert (euclidean__axioms.BetS q p c) as H27 by exact H24.
assert (* Cut *) (euclidean__axioms.Col q p c) as H28.
------- right.
right.
right.
right.
left.
exact H27.
------- assert (* Cut *) (~(p = r)) as H29.
-------- intro H29.
assert (* Cut *) (euclidean__axioms.Col q r d) as H30.
--------- right.
right.
right.
right.
left.
exact H25.
--------- assert (euclidean__axioms.Col q p c) as H31 by exact H28.
assert (* Cut *) (euclidean__axioms.Col q p d) as H32.
---------- apply (@eq__ind__r euclidean__axioms.Point r (fun p0 => (euclidean__axioms.Col A B p0) -> ((euclidean__axioms.BetS c p0 q) -> ((euclidean__axioms.BetS q p0 c) -> ((euclidean__axioms.BetS q p0 c) -> ((euclidean__axioms.Col q p0 c) -> ((euclidean__axioms.Col q p0 c) -> (euclidean__axioms.Col q p0 d)))))))) with (x := p).
-----------intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
exact H30.

----------- exact H29.
----------- exact H7.
----------- exact H11.
----------- exact H24.
----------- exact H27.
----------- exact H28.
----------- exact H31.
---------- assert (* Cut *) (euclidean__axioms.neq q p) as H33.
----------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H33.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal q p c H27).
------------ destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
----------- assert (* Cut *) (euclidean__axioms.Col p c d) as H34.
------------ apply (@euclidean__tactics.not__nCol__Col p c d).
-------------intro H34.
apply (@euclidean__tactics.Col__nCol__False p c d H34).
--------------apply (@lemma__collinear4.lemma__collinear4 q p c d H31 H32 H33).


------------ assert (* Cut *) (euclidean__axioms.Col c d p) as H35.
------------- assert (* Cut *) ((euclidean__axioms.Col c p d) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))))) as H35.
-------------- apply (@lemma__collinearorder.lemma__collinearorder p c d H34).
-------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H38.
------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H36.
-------------- exists p.
split.
--------------- exact H17.
--------------- split.
---------------- exact H19.
---------------- split.
----------------- exact H7.
----------------- exact H35.
-------------- apply (@H21 H36).
-------- assert (* Cut *) (euclidean__axioms.nCol p r c) as H30.
--------- apply (@euclidean__tactics.nCol__notCol p r c).
----------apply (@euclidean__tactics.nCol__not__Col p r c).
-----------apply (@lemma__NChelper.lemma__NChelper A B c p r H15 H7 H9 H29).


--------- assert (* Cut *) (euclidean__axioms.nCol p r d) as H31.
---------- apply (@euclidean__tactics.nCol__notCol p r d).
-----------apply (@euclidean__tactics.nCol__not__Col p r d).
------------apply (@lemma__NChelper.lemma__NChelper A B d p r H16 H7 H9 H29).


---------- assert (* Cut *) (euclidean__axioms.nCol r d p) as H32.
----------- assert (* Cut *) ((euclidean__axioms.nCol r p d) /\ ((euclidean__axioms.nCol r d p) /\ ((euclidean__axioms.nCol d p r) /\ ((euclidean__axioms.nCol p d r) /\ (euclidean__axioms.nCol d r p))))) as H32.
------------ apply (@lemma__NCorder.lemma__NCorder p r d H31).
------------ destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H35.
----------- assert (* Cut *) (euclidean__axioms.Col q r d) as H33.
------------ right.
right.
right.
right.
left.
exact H25.
------------ assert (* Cut *) (euclidean__axioms.Col r d q) as H34.
------------- assert (* Cut *) ((euclidean__axioms.Col r q d) /\ ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))))) as H34.
-------------- apply (@lemma__collinearorder.lemma__collinearorder q r d H33).
-------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H37.
------------- assert (* Cut *) (d = d) as H35.
-------------- apply (@logic.eq__refl Point d).
-------------- assert (* Cut *) (euclidean__axioms.Col r d d) as H36.
--------------- right.
right.
left.
exact H35.
--------------- assert (* Cut *) (euclidean__axioms.neq q d) as H37.
---------------- assert (* Cut *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H37.
----------------- apply (@lemma__betweennotequal.lemma__betweennotequal q r d H25).
----------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H41.
---------------- assert (* Cut *) (euclidean__axioms.nCol q d p) as H38.
----------------- apply (@euclidean__tactics.nCol__notCol q d p).
------------------apply (@euclidean__tactics.nCol__not__Col q d p).
-------------------apply (@lemma__NChelper.lemma__NChelper r d p q d H32 H34 H36 H37).


----------------- assert (* Cut *) (euclidean__axioms.nCol q p d) as H39.
------------------ assert (* Cut *) ((euclidean__axioms.nCol d q p) /\ ((euclidean__axioms.nCol d p q) /\ ((euclidean__axioms.nCol p q d) /\ ((euclidean__axioms.nCol q p d) /\ (euclidean__axioms.nCol p d q))))) as H39.
------------------- apply (@lemma__NCorder.lemma__NCorder q d p H38).
------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H46.
------------------ assert (euclidean__axioms.Col q p c) as H40 by exact H28.
assert (* Cut *) (c = c) as H41.
------------------- apply (@logic.eq__refl Point c).
------------------- assert (* Cut *) (~(c = p)) as H42.
-------------------- intro H42.
assert (* Cut *) (p = c) as H43.
--------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun c0 => (euclidean__defs.TP A B c0 d) -> ((euclidean__axioms.BetS c0 C d) -> ((euclidean__axioms.BetS d C c0) -> ((euclidean__axioms.neq c0 d) -> ((~(euclidean__defs.Meet A B c0 d)) -> ((euclidean__defs.OS c0 d A B) -> ((euclidean__axioms.BetS c0 p q) -> ((euclidean__axioms.nCol A B c0) -> ((euclidean__axioms.BetS q p c0) -> ((euclidean__axioms.BetS d C c0) -> ((euclidean__axioms.BetS q p c0) -> ((euclidean__axioms.Col q p c0) -> ((euclidean__axioms.nCol p r c0) -> ((euclidean__axioms.Col q p c0) -> ((c0 = c0) -> (p = c0))))))))))))))))) with (x := c).
----------------------intro H43.
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
exact H57.

---------------------- exact H42.
---------------------- exact H.
---------------------- exact H0.
---------------------- exact H1.
---------------------- exact H19.
---------------------- exact H21.
---------------------- exact H22.
---------------------- exact H11.
---------------------- exact H15.
---------------------- exact H24.
---------------------- exact H26.
---------------------- exact H27.
---------------------- exact H28.
---------------------- exact H30.
---------------------- exact H40.
---------------------- exact H41.
--------------------- assert (* Cut *) (euclidean__axioms.Col p r c) as H44.
---------------------- right.
left.
exact H43.
---------------------- apply (@euclidean__tactics.Col__nCol__False q p d H39).
-----------------------apply (@euclidean__tactics.not__nCol__Col q p d).
------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False p r c H30 H44).


-------------------- assert (* Cut *) (p = p) as H43.
--------------------- apply (@logic.eq__refl Point p).
--------------------- assert (* Cut *) (euclidean__axioms.Col q p p) as H44.
---------------------- right.
right.
left.
exact H43.
---------------------- assert (* Cut *) (euclidean__axioms.nCol c p d) as H45.
----------------------- apply (@euclidean__tactics.nCol__notCol c p d).
------------------------apply (@euclidean__tactics.nCol__not__Col c p d).
-------------------------apply (@lemma__NChelper.lemma__NChelper q p d c p H39 H40 H44 H42).


----------------------- assert (* Cut *) (euclidean__axioms.Col c p q) as H46.
------------------------ assert (* Cut *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H46.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder q p c H40).
------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H54.
------------------------ assert (c = c) as H47 by exact H41.
assert (* Cut *) (euclidean__axioms.Col c p c) as H48.
------------------------- right.
left.
exact H47.
------------------------- assert (* Cut *) (euclidean__axioms.neq q c) as H49.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H49.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal q p c H27).
--------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol q c d) as H50.
--------------------------- apply (@euclidean__tactics.nCol__notCol q c d).
----------------------------apply (@euclidean__tactics.nCol__not__Col q c d).
-----------------------------apply (@lemma__NChelper.lemma__NChelper c p d q c H45 H46 H48 H49).


--------------------------- assert (euclidean__axioms.BetS q p c) as H51 by exact H27.
assert (* Cut *) (exists E, (euclidean__axioms.BetS q E C) /\ (euclidean__axioms.BetS d E p)) as H52.
---------------------------- apply (@euclidean__axioms.postulate__Pasch__inner q d c p C H51 H26 H50).
---------------------------- destruct H52 as [E H53].
destruct H53 as [H54 H55].
assert (* Cut *) (euclidean__axioms.BetS p E d) as H56.
----------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry d E p H55).
----------------------------- assert (euclidean__axioms.BetS q r d) as H57 by exact H25.
assert (* Cut *) (exists F, (euclidean__axioms.BetS q F E) /\ (euclidean__axioms.BetS p F r)) as H58.
------------------------------ apply (@euclidean__axioms.postulate__Pasch__inner q p d r E H57 H56 H38).
------------------------------ destruct H58 as [F H59].
destruct H59 as [H60 H61].
assert (* Cut *) (euclidean__axioms.Col p r F) as H62.
------------------------------- right.
right.
right.
right.
right.
exact H61.
------------------------------- assert (* Cut *) (euclidean__axioms.Col B r p) as H63.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col B r p).
---------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False B r p H63).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 A B r p H9 H7 H17).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H64.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H64.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B p H7).
---------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H65.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A r) as H65.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H65.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B r H9).
----------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H66.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H66.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H17).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B p r) as H67.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))))) as H67.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B r p H63).
------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H74.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B p A) as H68.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H68.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A p H64).
-------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H75.
------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H69.
-------------------------------------- intro H69.
assert (* Cut *) (euclidean__axioms.Col c C d) as H70.
--------------------------------------- right.
right.
right.
right.
left.
exact H0.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col c d C) as H71.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d c C) /\ ((euclidean__axioms.Col c d C) /\ (euclidean__axioms.Col d C c))))) as H71.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder c C d H70).
----------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
---------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H72.
----------------------------------------- exists C.
split.
------------------------------------------ exact H17.
------------------------------------------ split.
------------------------------------------- exact H19.
------------------------------------------- split.
-------------------------------------------- exact H69.
-------------------------------------------- exact H71.
----------------------------------------- apply (@H21 H72).
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS q F C) as H70.
--------------------------------------- apply (@lemma__3__6b.lemma__3__6b q F E C H60 H54).
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C F q) as H71.
---------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry q F C H70).
---------------------------------------- assert (* Cut *) (~(~(euclidean__defs.OS C d A B))) as H72.
----------------------------------------- intro H72.
assert (* Cut *) (~(euclidean__axioms.neq B p)) as H73.
------------------------------------------ intro H73.
assert (* Cut *) (euclidean__axioms.Col p r A) as H74.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col p r A).
--------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False p r A H74).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 B p r A H67 H68 H73).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p r) as H75.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A p r) /\ ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p))))) as H75.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder p r A H74).
--------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H80.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p B) as H76.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H76.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B p A H68).
---------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H84.
--------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq A p)) as H77.
---------------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col p r B) as H78.
----------------------------------------------- apply (@euclidean__tactics.not__nCol__Col p r B).
------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False p r B H78).
-------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A p r B H75 H76 H77).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H79.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col A B F).
-------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False A B F H79).
--------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 p r A B F H29 H74 H78 H62).


------------------------------------------------ assert (* Cut *) (euclidean__defs.OS C d A B) as H80.
------------------------------------------------- exists q.
exists F.
exists r.
split.
-------------------------------------------------- exact H79.
-------------------------------------------------- split.
--------------------------------------------------- exact H9.
--------------------------------------------------- split.
---------------------------------------------------- exact H71.
---------------------------------------------------- split.
----------------------------------------------------- exact H13.
----------------------------------------------------- split.
------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol A B C H69).
------------------------------------------------------ exact H16.
------------------------------------------------- apply (@H69).
--------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B C).
---------------------------------------------------intro H81.
apply (@H72 H80).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A r F) as H78.
----------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun X => euclidean__axioms.Col X r F)) with (x := A).
------------------------------------------------ exact H62.
------------------------------------------------apply (@euclidean__tactics.NNPP (A = p) H77).

----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r A F) as H79.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r A F) /\ ((euclidean__axioms.Col r F A) /\ ((euclidean__axioms.Col F A r) /\ ((euclidean__axioms.Col A F r) /\ (euclidean__axioms.Col F r A))))) as H79.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A r F H78).
------------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H80.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r A B) as H80.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H80.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A r H65).
-------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H88.
------------------------------------------------- assert (* Cut *) (~(r = A)) as H81.
-------------------------------------------------- intro H81.
assert (* Cut *) (r = p) as H82.
--------------------------------------------------- assert (* Cut *) (A = p) as H82.
---------------------------------------------------- apply (@euclidean__tactics.NNPP (A = p) H77).
---------------------------------------------------- apply (@logic.eq__trans Point r A p H81 H82).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq p r) as H83.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H83.
----------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F q H71).
----------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H29.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq r p) as H84.
----------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric p r H83).
----------------------------------------------------- apply (@H69).
------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B C).
-------------------------------------------------------intro H85.
apply (@H84 H82).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F B) as H82.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A F B).
----------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False A F B H82).
-----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 r A F B H79 H80 H81).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H83.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H83.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F B H82).
----------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H90.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H84.
----------------------------------------------------- exists q.
exists F.
exists r.
split.
------------------------------------------------------ exact H83.
------------------------------------------------------ split.
------------------------------------------------------- exact H9.
------------------------------------------------------- split.
-------------------------------------------------------- exact H71.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H13.
--------------------------------------------------------- split.
---------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A B C H69).
---------------------------------------------------------- exact H16.
----------------------------------------------------- apply (@H69).
------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B C).
-------------------------------------------------------intro H85.
apply (@H72 H84).


------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A p) as H74.
------------------------------------------- assert (* Cut *) (B = p) as H74.
-------------------------------------------- apply (@euclidean__tactics.NNPP (B = p) H73).
-------------------------------------------- intro H75.
assert (* Cut *) (A = B) as Heq.
--------------------------------------------- apply (@logic.eq__trans Point A p B H75).
----------------------------------------------apply (@logic.eq__sym Point B p H74).

--------------------------------------------- assert False.
----------------------------------------------apply (@H17 Heq).
---------------------------------------------- contradiction.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p B) as H75.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H75.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B p A H68).
--------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H83.
-------------------------------------------- assert (* Cut *) (A = A) as H76.
--------------------------------------------- apply (@logic.eq__refl Point A).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A A) as H77.
---------------------------------------------- right.
right.
left.
exact H76.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H78.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B A) /\ ((euclidean__axioms.Col A A B) /\ ((euclidean__axioms.Col A B A) /\ ((euclidean__axioms.Col B A A) /\ (euclidean__axioms.Col A A B))))) as H78.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B A A H77).
------------------------------------------------ destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H64.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A r) as H79.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H79.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A p H78).
------------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H65.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A p r) as H80.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A p r).
--------------------------------------------------intro H80.
apply (@euclidean__tactics.Col__nCol__False A p r H80).
---------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 B A A p r H66 H77 H78 H79).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p B r) as H81.
-------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col p B r).
---------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False p B r H81).
----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A p B r H75 H80 H74).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r B) as H82.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B p r) /\ ((euclidean__axioms.Col B r p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p r B) /\ (euclidean__axioms.Col r B p))))) as H82.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder p B r H81).
---------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H89.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r A) as H83.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col p r A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A))))) as H83.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A p r H80).
----------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H86.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H84.
----------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A B F).
------------------------------------------------------intro H84.
apply (@euclidean__tactics.Col__nCol__False A B F H84).
-------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 p r A B F H29 H83 H82 H62).


----------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H85.
------------------------------------------------------ exists q.
exists F.
exists r.
split.
------------------------------------------------------- exact H84.
------------------------------------------------------- split.
-------------------------------------------------------- exact H9.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H71.
--------------------------------------------------------- split.
---------------------------------------------------------- exact H13.
---------------------------------------------------------- split.
----------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A B C H69).
----------------------------------------------------------- exact H16.
------------------------------------------------------ apply (@H69).
-------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A B C).
--------------------------------------------------------intro H86.
apply (@H72 H85).


----------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C d)) as H73.
------------------------------------------ intro H73.
assert (exists R, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.Col C d R)))) as H74 by exact H73.
destruct H74 as [R H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
assert (* Cut *) (euclidean__axioms.Col c C d) as H82.
------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H82.
-------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.OS C d A B) H72).
-------------------------------------------- right.
right.
right.
right.
left.
exact H0.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C d c) as H83.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d c C) /\ ((euclidean__axioms.Col c d C) /\ (euclidean__axioms.Col d C c))))) as H83.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder c C d H82).
--------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H86.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H84.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H84.
---------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F q H71).
---------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H78.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d c R) as H85.
---------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H85.
----------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.OS C d A B) H72).
----------------------------------------------- apply (@euclidean__tactics.not__nCol__Col d c R).
------------------------------------------------intro H86.
apply (@euclidean__tactics.Col__nCol__False d c R H86).
-------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C d c R H83 H81 H84).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c d R) as H86.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c d R) /\ ((euclidean__axioms.Col c R d) /\ ((euclidean__axioms.Col R d c) /\ ((euclidean__axioms.Col d R c) /\ (euclidean__axioms.Col R c d))))) as H86.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder d c R H85).
------------------------------------------------ destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
exact H87.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H87.
------------------------------------------------ assert (* Cut *) (euclidean__defs.OS C d A B) as H87.
------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.OS C d A B) H72).
------------------------------------------------- exists R.
split.
-------------------------------------------------- exact H76.
-------------------------------------------------- split.
--------------------------------------------------- exact H19.
--------------------------------------------------- split.
---------------------------------------------------- exact H80.
---------------------------------------------------- exact H86.
------------------------------------------------ apply (@H21 H87).
------------------------------------------ assert (* Cut *) (euclidean__defs.TP A B C d) as H74.
------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H74.
-------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.OS C d A B) H72).
-------------------------------------------- split.
--------------------------------------------- exact H17.
--------------------------------------------- split.
---------------------------------------------- exact H23.
---------------------------------------------- split.
----------------------------------------------- exact H73.
----------------------------------------------- exact H74.
------------------------------------------- exact H74.
Qed.
