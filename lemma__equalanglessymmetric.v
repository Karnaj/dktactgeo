Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinearitypreserved.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__doublereverse.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray2.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__equalanglessymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.CongA A B C a b c) -> (euclidean__defs.CongA a b c A B C).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H0.
- exact H.
- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H1.
-- exact H0.
-- destruct H1 as [U H1].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H2.
--- exact H1.
--- destruct H2 as [V H2].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H3.
---- exact H2.
---- destruct H3 as [u H3].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H4.
----- exact H3.
----- destruct H4 as [v H4].
assert (* AndElim *) ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* Cut *) (euclidean__axioms.Cong b u B U) as H19.
------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (b) (B) (U) (u) H13).
------------- assert (* Cut *) (euclidean__axioms.Cong b v B V) as H20.
-------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (b) (B) (V) (v) H15).
-------------- assert (* Cut *) (euclidean__axioms.Cong v u V U) as H21.
--------------- assert (* Cut *) ((euclidean__axioms.Cong v u V U) /\ (euclidean__axioms.Cong V U v u)) as H21.
---------------- apply (@lemma__doublereverse.lemma__doublereverse (U) (V) (u) (v) H17).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong v u V U) /\ (euclidean__axioms.Cong V U v u)) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
exact H22.
--------------- assert (* Cut *) (~(euclidean__axioms.Col a b c)) as H22.
---------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col b a u) as H23.
----------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (b) (a) (u) H9).
----------------- assert (* Cut *) (euclidean__axioms.Col b c v) as H24.
------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (b) (c) (v) H11).
------------------ assert (* Cut *) (euclidean__axioms.Col B A U) as H25.
------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (A) (U) H5).
------------------- assert (* Cut *) (euclidean__axioms.Col B C V) as H26.
-------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (C) (V) H7).
-------------------- assert (* Cut *) (euclidean__axioms.Col a b u) as H27.
--------------------- assert (* Cut *) ((euclidean__axioms.Col a b u) /\ ((euclidean__axioms.Col a u b) /\ ((euclidean__axioms.Col u b a) /\ ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b))))) as H27.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (b) (a) (u) H23).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col a b u) /\ ((euclidean__axioms.Col a u b) /\ ((euclidean__axioms.Col u b a) /\ ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b))))) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col a u b) /\ ((euclidean__axioms.Col u b a) /\ ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b)))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col u b a) /\ ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col b u a) /\ (euclidean__axioms.Col u a b)) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
exact H28.
--------------------- assert (* Cut *) (euclidean__axioms.neq b a) as H28.
---------------------- apply (@lemma__ray2.lemma__ray2 (b) (a) (u) H9).
---------------------- assert (* Cut *) (euclidean__axioms.neq a b) as H29.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (b) (a) H28).
----------------------- assert (* Cut *) (euclidean__axioms.Col b u c) as H30.
------------------------ apply (@euclidean__tactics.not__nCol__Col (b) (u) (c)).
-------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False (b) (u) (c) (H30)).
--------------------------apply (@lemma__collinear4.lemma__collinear4 (a) (b) (u) (c) (H27) (H22) H29).


------------------------ assert (* Cut *) (euclidean__axioms.Col c b u) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.Col u b c) /\ ((euclidean__axioms.Col u c b) /\ ((euclidean__axioms.Col c b u) /\ ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b))))) as H31.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (b) (u) (c) H30).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col u b c) /\ ((euclidean__axioms.Col u c b) /\ ((euclidean__axioms.Col c b u) /\ ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b))))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col u c b) /\ ((euclidean__axioms.Col c b u) /\ ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b)))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col c b u) /\ ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col b c u) /\ (euclidean__axioms.Col c u b)) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
exact H36.
------------------------- assert (* Cut *) (euclidean__axioms.Col c b v) as H32.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col c b v) /\ ((euclidean__axioms.Col c v b) /\ ((euclidean__axioms.Col v b c) /\ ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b))))) as H32.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (b) (c) (v) H24).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col c b v) /\ ((euclidean__axioms.Col c v b) /\ ((euclidean__axioms.Col v b c) /\ ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col c v b) /\ ((euclidean__axioms.Col v b c) /\ ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b)))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col v b c) /\ ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col b v c) /\ (euclidean__axioms.Col v c b)) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
exact H33.
-------------------------- assert (* Cut *) (euclidean__axioms.neq b c) as H33.
--------------------------- apply (@lemma__ray2.lemma__ray2 (b) (c) (v) H11).
--------------------------- assert (* Cut *) (euclidean__axioms.neq c b) as H34.
---------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (b) (c) H33).
---------------------------- assert (* Cut *) (euclidean__axioms.Col b u v) as H35.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (b) (u) (v)).
------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (b) (u) (v) (H35)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (c) (b) (u) (v) (H31) (H32) H34).


----------------------------- assert (* Cut *) (euclidean__axioms.Cong u v U V) as H36.
------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (u) (U) (V) (v) H17).
------------------------------ assert (* Cut *) (euclidean__axioms.Col B U V) as H37.
------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (U) (V)).
--------------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False (B) (U) (V) (H37)).
---------------------------------apply (@lemma__collinearitypreserved.lemma__collinearitypreserved (b) (u) (v) (B) (U) (V) (H35) (H19) (H20) H36).


------------------------------- assert (* Cut *) (euclidean__axioms.Col U B V) as H38.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col U B V) /\ ((euclidean__axioms.Col U V B) /\ ((euclidean__axioms.Col V B U) /\ ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B))))) as H38.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (U) (V) H37).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col U B V) /\ ((euclidean__axioms.Col U V B) /\ ((euclidean__axioms.Col V B U) /\ ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B))))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col U V B) /\ ((euclidean__axioms.Col V B U) /\ ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B)))) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col V B U) /\ ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B))) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B V U) /\ (euclidean__axioms.Col V U B)) as H45.
------------------------------------- exact H44.
------------------------------------- destruct H45 as [H45 H46].
exact H39.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col U B A) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (U) H25).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A U B) /\ ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col U B A) /\ ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col B U A) /\ (euclidean__axioms.Col U A B)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H44.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq B U) as H40.
---------------------------------- apply (@lemma__raystrict.lemma__raystrict (B) (A) (U) H5).
---------------------------------- assert (* Cut *) (euclidean__axioms.neq U B) as H41.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (U) H40).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B V A) as H42.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (V) (A)).
-------------------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False (B) (V) (A) (H42)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (U) (B) (V) (A) (H38) (H39) H41).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col V B A) as H43.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col V B A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B))))) as H43.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (V) (A) H42).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col V B A) /\ ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B))))) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col V A B) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B)))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B A V) /\ (euclidean__axioms.Col A V B)) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
exact H44.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col V B C) as H44.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B V) /\ ((euclidean__axioms.Col C V B) /\ ((euclidean__axioms.Col V B C) /\ ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B))))) as H44.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (V) H26).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B V) /\ ((euclidean__axioms.Col C V B) /\ ((euclidean__axioms.Col V B C) /\ ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B))))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C V B) /\ ((euclidean__axioms.Col V B C) /\ ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B)))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col V B C) /\ ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col B V C) /\ (euclidean__axioms.Col V C B)) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
exact H49.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq B V) as H45.
--------------------------------------- apply (@lemma__raystrict.lemma__raystrict (B) (C) (V) H7).
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq V B) as H46.
---------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (V) H45).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H47.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------------------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H47)).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (V) (B) (A) (C) (H43) (H44) H46).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H48.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H48.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H47).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H55.
----------------------------------------------- exact H54.
----------------------------------------------- destruct H55 as [H55 H56].
exact H49.
------------------------------------------ apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H18) H48).
---------------- assert (* Cut *) (euclidean__axioms.Cong u v U V) as H23.
----------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (u) (U) (V) (v) H17).
----------------- assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H24.
------------------ exists u.
exists v.
exists U.
exists V.
split.
------------------- exact H9.
------------------- split.
-------------------- exact H11.
-------------------- split.
--------------------- exact H5.
--------------------- split.
---------------------- exact H7.
---------------------- split.
----------------------- exact H19.
----------------------- split.
------------------------ exact H20.
------------------------ split.
------------------------- exact H23.
------------------------- apply (@euclidean__tactics.nCol__notCol (a) (b) (c) H22).
------------------ exact H24.
Qed.
