Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Definition proposition__08 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D E F) -> ((euclidean__axioms.Cong A B D E) -> ((euclidean__axioms.Cong A C D F) -> ((euclidean__axioms.Cong B C E F) -> ((euclidean__defs.CongA B A C E D F) /\ ((euclidean__defs.CongA C B A F E D) /\ (euclidean__defs.CongA A C B D F E))))))).
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
assert (* Cut *) (E = E) as H4.
- apply (@logic.eq__refl (Point) E).
- assert (* Cut *) (F = F) as H5.
-- apply (@logic.eq__refl (Point) F).
-- assert (* Cut *) (B = B) as H6.
--- apply (@logic.eq__refl (Point) B).
--- assert (* Cut *) (C = C) as H7.
---- apply (@logic.eq__refl (Point) C).
---- assert (* Cut *) (D = D) as H8.
----- apply (@logic.eq__refl (Point) D).
----- assert (* Cut *) (A = A) as H9.
------ apply (@logic.eq__refl (Point) A).
------ assert (* Cut *) (euclidean__axioms.nCol A B C) as H10.
------- exact H.
------- assert (* Cut *) (euclidean__axioms.nCol D E F) as H11.
-------- exact H0.
-------- assert (* Cut *) (~(A = B)) as H12.
--------- intro H12.
assert (* Cut *) (euclidean__axioms.Col A B C) as H13.
---------- left.
exact H12.
---------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11)).
-----------apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
------------intro H14.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H13).


--------- assert (* Cut *) (euclidean__axioms.neq B A) as H13.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H12).
---------- assert (* Cut *) (~(B = C)) as H14.
----------- intro H14.
assert (* Cut *) (euclidean__axioms.Col A B C) as H15.
------------ right.
right.
left.
exact H14.
------------ apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11)).
-------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
--------------intro H16.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H15).


----------- assert (* Cut *) (euclidean__axioms.neq C B) as H15.
------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H14).
------------ assert (* Cut *) (~(D = E)) as H16.
------------- intro H16.
assert (* Cut *) (euclidean__axioms.Col D E F) as H17.
-------------- left.
exact H16.
-------------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11) H17).
------------- assert (* Cut *) (euclidean__axioms.neq E D) as H17.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H16).
-------------- assert (* Cut *) (~(A = C)) as H18.
--------------- intro H18.
assert (* Cut *) (euclidean__axioms.Col A B C) as H19.
---------------- right.
left.
exact H18.
---------------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11)).
-----------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
------------------intro H20.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H19).


--------------- assert (* Cut *) (euclidean__axioms.neq C A) as H19.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H18).
---------------- assert (* Cut *) (~(D = F)) as H20.
----------------- intro H20.
assert (* Cut *) (euclidean__axioms.Col D E F) as H21.
------------------ right.
left.
exact H20.
------------------ apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11) H21).
----------------- assert (* Cut *) (euclidean__axioms.neq F D) as H21.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (F) H20).
------------------ assert (* Cut *) (~(E = F)) as H22.
------------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col D E F) as H23.
-------------------- right.
right.
left.
exact H22.
-------------------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11) H23).
------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H23.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H22).
-------------------- assert (* Cut *) (euclidean__defs.Out D E E) as H24.
--------------------- apply (@lemma__ray4.lemma__ray4 (D) (E) (E)).
----------------------right.
left.
exact H4.

---------------------- exact H16.
--------------------- assert (* Cut *) (euclidean__defs.Out D F F) as H25.
---------------------- apply (@lemma__ray4.lemma__ray4 (D) (F) (F)).
-----------------------right.
left.
exact H5.

----------------------- exact H20.
---------------------- assert (* Cut *) (euclidean__defs.Out A B B) as H26.
----------------------- apply (@lemma__ray4.lemma__ray4 (A) (B) (B)).
------------------------right.
left.
exact H6.

------------------------ exact H12.
----------------------- assert (* Cut *) (euclidean__defs.Out A C C) as H27.
------------------------ apply (@lemma__ray4.lemma__ray4 (A) (C) (C)).
-------------------------right.
left.
exact H7.

------------------------- exact H18.
------------------------ assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H28.
------------------------- intro H28.
assert (* Cut *) (euclidean__axioms.Col A B C) as H29.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H29.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H28).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
exact H30.
-------------------------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H11)).
---------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (F)).
----------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H29).


------------------------- assert (* Cut *) (euclidean__defs.CongA B A C E D F) as H29.
-------------------------- exists B.
exists C.
exists E.
exists F.
split.
--------------------------- exact H26.
--------------------------- split.
---------------------------- exact H27.
---------------------------- split.
----------------------------- exact H24.
----------------------------- split.
------------------------------ exact H25.
------------------------------ split.
------------------------------- exact H1.
------------------------------- split.
-------------------------------- exact H2.
-------------------------------- split.
--------------------------------- exact H3.
--------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (A) (C) H28).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong B A E D) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H30.
---------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (E) H1).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D)) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
exact H31.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong C A F D) as H31.
---------------------------- assert (* Cut *) ((euclidean__axioms.Cong C A F D) /\ ((euclidean__axioms.Cong C A D F) /\ (euclidean__axioms.Cong A C F D))) as H31.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (D) (F) H2).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C A F D) /\ ((euclidean__axioms.Cong C A D F) /\ (euclidean__axioms.Cong A C F D))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Cong C A D F) /\ (euclidean__axioms.Cong A C F D)) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
exact H32.
---------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H32.
----------------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (F)).
------------------------------right.
left.
exact H5.

------------------------------ exact H22.
----------------------------- assert (* Cut *) (euclidean__defs.Out E D D) as H33.
------------------------------ apply (@lemma__ray4.lemma__ray4 (E) (D) (D)).
-------------------------------right.
left.
exact H8.

------------------------------- exact H17.
------------------------------ assert (* Cut *) (euclidean__defs.Out B C C) as H34.
------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
--------------------------------right.
left.
exact H7.

-------------------------------- exact H14.
------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H35.
-------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
---------------------------------right.
left.
exact H9.

--------------------------------- exact H13.
-------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H36.
--------------------------------- intro H36.
assert (* Cut *) (euclidean__axioms.Col A B C) as H37.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H37.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H36).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
exact H45.
---------------------------------- apply (@H28).
-----------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H37).


--------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A F E D) as H37.
---------------------------------- exists C.
exists A.
exists F.
exists D.
split.
----------------------------------- exact H34.
----------------------------------- split.
------------------------------------ exact H35.
------------------------------------ split.
------------------------------------- exact H32.
------------------------------------- split.
-------------------------------------- exact H33.
-------------------------------------- split.
--------------------------------------- exact H3.
--------------------------------------- split.
---------------------------------------- exact H30.
---------------------------------------- split.
----------------------------------------- exact H31.
----------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H36).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A F D) as H38.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A B D E) /\ ((euclidean__axioms.Cong A B E D) /\ (euclidean__axioms.Cong B A D E))) as H38.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (B) (A) (E) (D) H30).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A B D E) /\ ((euclidean__axioms.Cong A B E D) /\ (euclidean__axioms.Cong B A D E))) as H39.
------------------------------------- exact H38.
------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong A B E D) /\ (euclidean__axioms.Cong B A D E)) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [H41 H42].
exact H31.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B F E) as H39.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong C B F E) /\ ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E))) as H39.
------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (E) (F) H3).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C B F E) /\ ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E))) as H40.
-------------------------------------- exact H39.
-------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E)) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [H42 H43].
exact H40.
------------------------------------ assert (* Cut *) (euclidean__defs.Out F D D) as H40.
------------------------------------- apply (@lemma__ray4.lemma__ray4 (F) (D) (D)).
--------------------------------------right.
left.
exact H8.

-------------------------------------- exact H21.
------------------------------------- assert (* Cut *) (euclidean__defs.Out F E E) as H41.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 (F) (E) (E)).
---------------------------------------right.
left.
exact H4.

--------------------------------------- exact H23.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H42.
--------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
----------------------------------------right.
left.
exact H9.

---------------------------------------- exact H19.
--------------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H43.
---------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
-----------------------------------------right.
left.
exact H6.

----------------------------------------- exact H15.
---------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H44.
----------------------------------------- intro H44.
assert (* Cut *) (euclidean__axioms.Col A B C) as H45.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H45.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H44).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H46.
-------------------------------------------- exact H45.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
exact H52.
------------------------------------------ apply (@H28).
-------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H45).


----------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C B D F E) as H45.
------------------------------------------ exists A.
exists B.
exists D.
exists E.
split.
------------------------------------------- exact H42.
------------------------------------------- split.
-------------------------------------------- exact H43.
-------------------------------------------- split.
--------------------------------------------- exact H40.
--------------------------------------------- split.
---------------------------------------------- exact H41.
---------------------------------------------- split.
----------------------------------------------- exact H38.
----------------------------------------------- split.
------------------------------------------------ exact H39.
------------------------------------------------ split.
------------------------------------------------- exact H1.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H44).
------------------------------------------ split.
------------------------------------------- exact H29.
------------------------------------------- split.
-------------------------------------------- exact H37.
-------------------------------------------- exact H45.
Qed.
