Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGrotate.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__planeseparation.
Require Export lemma__samesidecollinear.
Require Export lemma__samesideflip.
Require Export logic.
Require Export proposition__10.
Require Export proposition__23C.
Require Export proposition__42B.
Require Export proposition__44A.
Definition proposition__44 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (D: euclidean__axioms.Point) (J: euclidean__axioms.Point) (N: euclidean__axioms.Point) (R: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Triangle a b c) -> ((euclidean__axioms.nCol J D N) -> ((euclidean__axioms.nCol A B R) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point), (euclidean__defs.PG A B X Y) /\ ((euclidean__defs.CongA A B X J D N) /\ ((euclidean__axioms.EF a b Z c A B X Y) /\ ((euclidean__defs.Midpoint b Z c) /\ (euclidean__axioms.TS X A B R))))))).
Proof.
intro A.
intro B.
intro D.
intro J.
intro N.
intro R.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq A B) as H2.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A)))))) as H2.
-- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (R) H1).
-- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A)))))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A))))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A)))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq R B) /\ (euclidean__axioms.neq R A)) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
exact H3.
- assert (* Cut *) (euclidean__axioms.nCol a b c) as H3.
-- exact H.
-- assert (* Cut *) (euclidean__axioms.neq b c) as H4.
--- assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))))) as H4.
---- apply (@lemma__NCdistinct.lemma__NCdistinct (a) (b) (c) H3).
---- assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
exact H7.
--- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS b m c) /\ (euclidean__axioms.Cong m b m c)) as H5.
---- apply (@proposition__10.proposition__10 (b) (c) H4).
---- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS b m c) /\ (euclidean__axioms.Cong m b m c))) as H6.
----- exact H5.
----- destruct H6 as [m H6].
assert (* AndElim *) ((euclidean__axioms.BetS b m c) /\ (euclidean__axioms.Cong m b m c)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Cong b m m c) as H9.
------- assert (* Cut *) ((euclidean__axioms.Cong b m c m) /\ ((euclidean__axioms.Cong b m m c) /\ (euclidean__axioms.Cong m b c m))) as H9.
-------- apply (@lemma__congruenceflip.lemma__congruenceflip (m) (b) (m) (c) H8).
-------- assert (* AndElim *) ((euclidean__axioms.Cong b m c m) /\ ((euclidean__axioms.Cong b m m c) /\ (euclidean__axioms.Cong m b c m))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Cong b m m c) /\ (euclidean__axioms.Cong m b c m)) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
exact H12.
------- assert (* Cut *) (euclidean__defs.Midpoint b m c) as H10.
-------- split.
--------- exact H7.
--------- exact H9.
-------- assert (* Cut *) (euclidean__axioms.neq m c) as H11.
--------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H11.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (b) (m) (c) H7).
---------- assert (* AndElim *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
exact H12.
--------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E m c)) as H12.
---------- apply (@lemma__extension.lemma__extension (A) (B) (m) (c) (H2) H11).
---------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E m c))) as H13.
----------- exact H12.
----------- destruct H13 as [E H13].
assert (* AndElim *) ((euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E m c)) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.neq B E) as H16.
------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H16.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H14).
-------------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H17.
------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H17.
-------------- right.
right.
right.
right.
left.
exact H14.
-------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H18.
--------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H18.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (E) H17).
---------------- assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
exact H19.
--------------- assert (* Cut *) (B = B) as H19.
---------------- apply (@logic.eq__refl (Point) B).
---------------- assert (* Cut *) (euclidean__axioms.Col B A B) as H20.
----------------- right.
left.
exact H19.
----------------- assert (* Cut *) (euclidean__axioms.nCol B A R) as H21.
------------------ assert (* Cut *) ((euclidean__axioms.nCol B A R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))))) as H21.
------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (R) H1).
------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A)))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A)) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
exact H22.
------------------ assert (* Cut *) (euclidean__axioms.nCol B E R) as H22.
------------------- apply (@euclidean__tactics.nCol__notCol (B) (E) (R)).
--------------------apply (@euclidean__tactics.nCol__not__Col (B) (E) (R)).
---------------------apply (@lemma__NChelper.lemma__NChelper (B) (A) (R) (B) (E) (H21) (H20) (H18) H16).


------------------- assert (* Cut *) (exists (g: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Out B E e) /\ ((euclidean__defs.CongA g B e J D N) /\ (euclidean__defs.OS g R B E))) as H23.
-------------------- apply (@proposition__23C.proposition__23C (B) (E) (D) (J) (N) (R) (H16) (H0) H22).
-------------------- assert (exists g: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Out B E e) /\ ((euclidean__defs.CongA g B e J D N) /\ (euclidean__defs.OS g R B E)))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [g H24].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Out B E e) /\ ((euclidean__defs.CongA g B e J D N) /\ (euclidean__defs.OS g R B E)))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [e H25].
assert (* AndElim *) ((euclidean__defs.Out B E e) /\ ((euclidean__defs.CongA g B e J D N) /\ (euclidean__defs.OS g R B E))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.CongA g B e J D N) /\ (euclidean__defs.OS g R B E)) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* Cut *) (euclidean__axioms.neq B A) as H30.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H2).
------------------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P B A)) as H31.
-------------------------- apply (@lemma__extension.lemma__extension (B) (A) (B) (A) (H30) H30).
-------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P B A))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [P H32].
assert (* AndElim *) ((euclidean__axioms.BetS B A P) /\ (euclidean__axioms.Cong A P B A)) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__axioms.neq B E) as H35.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P))) as H35.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (P) H33).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B P)) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
exact H16.
----------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H36.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H35).
------------------------------ assert (* Cut *) (euclidean__axioms.neq b m) as H37.
------------------------------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H37.
-------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (b) (m) (c) H7).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq b m) /\ (euclidean__axioms.neq b c)) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
exact H40.
------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS E B Q) /\ (euclidean__axioms.Cong B Q b m)) as H38.
-------------------------------- apply (@lemma__extension.lemma__extension (E) (B) (b) (m) (H36) H37).
-------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS E B Q) /\ (euclidean__axioms.Cong B Q b m))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [Q H39].
assert (* AndElim *) ((euclidean__axioms.BetS E B Q) /\ (euclidean__axioms.Cong B Q b m)) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) (euclidean__axioms.Cong b m m c) as H42.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Cong Q B m b) /\ ((euclidean__axioms.Cong Q B b m) /\ (euclidean__axioms.Cong B Q m b))) as H42.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (B) (Q) (b) (m) H41).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong Q B m b) /\ ((euclidean__axioms.Cong Q B b m) /\ (euclidean__axioms.Cong B Q m b))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong Q B b m) /\ (euclidean__axioms.Cong B Q m b)) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
exact H9.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q m c) as H43.
------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (Q) (b) (m) (m) (c) (H41) H42).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong m c B E) as H44.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (m) (B) (E) (c) H15).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B Q B E) as H45.
-------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (Q) (m) (c) (B) (E) (H43) H44).
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS Q B E) as H46.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (B) (Q) H40).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q B B E) as H47.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong Q B E B) /\ ((euclidean__axioms.Cong Q B B E) /\ (euclidean__axioms.Cong B Q E B))) as H47.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (Q) (B) (E) H45).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong Q B E B) /\ ((euclidean__axioms.Cong Q B B E) /\ (euclidean__axioms.Cong B Q E B))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Cong Q B B E) /\ (euclidean__axioms.Cong B Q E B)) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
exact H50.
---------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint Q B E) as H48.
----------------------------------------- split.
------------------------------------------ exact H46.
------------------------------------------ exact H47.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A R) as H49.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E B R) /\ ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))))) as H49.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (E) (R) H22).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B R) /\ ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B)))) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B)) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
exact H21.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B E) as H50.
------------------------------------------- exact H17.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H51.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H51.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (E) H50).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H52.
---------------------------------------------- exact H51.
---------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)))) as H54.
----------------------------------------------- exact H53.
----------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))) as H56.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
exact H52.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H52.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq Q B) /\ (euclidean__axioms.neq Q E))) as H52.
---------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (B) (E) H46).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq Q B) /\ (euclidean__axioms.neq Q E))) as H53.
----------------------------------------------- exact H52.
----------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq Q B) /\ (euclidean__axioms.neq Q E)) as H55.
------------------------------------------------ exact H54.
------------------------------------------------ destruct H55 as [H55 H56].
exact H53.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E R) as H53.
---------------------------------------------- exact H22.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol R B E) as H54.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B R) /\ ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))))) as H54.
------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (B) (E) (R) H53).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol E B R) /\ ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))))) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.nCol E R B) /\ ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B)))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol R B E) /\ ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol B R E) /\ (euclidean__axioms.nCol R E B)) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
exact H59.
----------------------------------------------- assert (* Cut *) (exists (G: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.PG G B E F) /\ ((euclidean__axioms.EF a b m c G B E F) /\ ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E)))) as H55.
------------------------------------------------ apply (@proposition__42B.proposition__42B (Q) (E) (D) (B) (J) (N) (R) (a) (b) (c) (m) (H3) (H10) (H0) (H48) (H15) H54).
------------------------------------------------ assert (exists G: euclidean__axioms.Point, (exists (F: euclidean__axioms.Point), (euclidean__defs.PG G B E F) /\ ((euclidean__axioms.EF a b m c G B E F) /\ ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E))))) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [G H56].
assert (exists F: euclidean__axioms.Point, ((euclidean__defs.PG G B E F) /\ ((euclidean__axioms.EF a b m c G B E F) /\ ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E))))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [F H57].
assert (* AndElim *) ((euclidean__defs.PG G B E F) /\ ((euclidean__axioms.EF a b m c G B E F) /\ ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E)))) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.EF a b m c G B E F) /\ ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__defs.CongA E B G J D N) /\ (euclidean__defs.OS R G B E)) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* Cut *) (euclidean__defs.PG B E F G) as H64.
------------------------------------------------------ apply (@lemma__PGrotate.lemma__PGrotate (G) (B) (E) (F) H58).
------------------------------------------------------ assert (* Cut *) (exists (M: euclidean__axioms.Point) (L: euclidean__axioms.Point), (euclidean__defs.PG A B M L) /\ ((euclidean__defs.CongA A B M J D N) /\ ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M)))) as H65.
------------------------------------------------------- apply (@proposition__44A.proposition__44A (A) (B) (D) (E) (F) (G) (J) (N) (H64) (H62) H14).
------------------------------------------------------- assert (exists M: euclidean__axioms.Point, (exists (L: euclidean__axioms.Point), (euclidean__defs.PG A B M L) /\ ((euclidean__defs.CongA A B M J D N) /\ ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M))))) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [M H66].
assert (exists L: euclidean__axioms.Point, ((euclidean__defs.PG A B M L) /\ ((euclidean__defs.CongA A B M J D N) /\ ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M))))) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [L H67].
assert (* AndElim *) ((euclidean__defs.PG A B M L) /\ ((euclidean__defs.CongA A B M J D N) /\ ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M)))) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__defs.CongA A B M J D N) /\ ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M))) as H70.
----------------------------------------------------------- exact H69.
----------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.EF B E F G L M B A) /\ (euclidean__axioms.BetS G B M)) as H72.
------------------------------------------------------------ exact H71.
------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* Cut *) (B = B) as H74.
------------------------------------------------------------- exact H19.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H75.
-------------------------------------------------------------- right.
right.
left.
exact H74.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B E F) as H76.
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par A B M L) /\ (euclidean__defs.Par A L B M)) as H76.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__defs.Par B E F G) /\ (euclidean__defs.Par B G E F)) as H78.
----------------------------------------------------------------- exact H64.
----------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__defs.Par G B E F) /\ (euclidean__defs.Par G F B E)) as H80.
------------------------------------------------------------------ exact H58.
------------------------------------------------------------------ destruct H80 as [H80 H81].
exact H80.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G B E) as H77.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G B E) /\ ((euclidean__axioms.nCol G E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol G B F)))) as H77.
----------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (G) (B) (E) (F) H76).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G B E) /\ ((euclidean__axioms.nCol G E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol G B F)))) as H78.
------------------------------------------------------------------ exact H77.
------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol G E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol G B F))) as H80.
------------------------------------------------------------------- exact H79.
------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol G B F)) as H82.
-------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H78.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B G) as H78.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B G E) /\ ((euclidean__axioms.nCol B E G) /\ ((euclidean__axioms.nCol E G B) /\ ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G))))) as H78.
------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (G) (B) (E) H77).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B G E) /\ ((euclidean__axioms.nCol B E G) /\ ((euclidean__axioms.nCol E G B) /\ ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G))))) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol B E G) /\ ((euclidean__axioms.nCol E G B) /\ ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G)))) as H81.
-------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol E G B) /\ ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G))) as H83.
--------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G)) as H85.
---------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H86.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B A) as H79.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H79.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (E) H51).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)))) as H82.
--------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))) as H84.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)) as H86.
----------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H84.
------------------------------------------------------------------ assert (* Cut *) (B = B) as H80.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B B) as H81.
-------------------------------------------------------------------- right.
right.
left.
exact H80.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B G) as H82.
--------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (G)).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (B) (G)).
-----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (E) (B) (G) (A) (B) (H78) (H79) (H81) H2).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G A B M) as H83.
---------------------------------------------------------------------- exists B.
split.
----------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------- split.
------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------ exact H82.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b m c B E F G) as H84.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF a b m c B E F G) /\ ((euclidean__axioms.EF a b m c F E B G) /\ ((euclidean__axioms.EF a b m c E F G B) /\ ((euclidean__axioms.EF a b m c B G F E) /\ ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B))))))) as H84.
------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation (a) (b) (m) (c) (G) (B) (E) (F) H60).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.EF a b m c B E F G) /\ ((euclidean__axioms.EF a b m c F E B G) /\ ((euclidean__axioms.EF a b m c E F G B) /\ ((euclidean__axioms.EF a b m c B G F E) /\ ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B))))))) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.EF a b m c F E B G) /\ ((euclidean__axioms.EF a b m c E F G B) /\ ((euclidean__axioms.EF a b m c B G F E) /\ ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B)))))) as H87.
-------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.EF a b m c E F G B) /\ ((euclidean__axioms.EF a b m c B G F E) /\ ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B))))) as H89.
--------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.EF a b m c B G F E) /\ ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B)))) as H91.
---------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.EF a b m c F G B E) /\ ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B))) as H93.
----------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.EF a b m c E B G F) /\ (euclidean__axioms.EF a b m c G F E B)) as H95.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ destruct H95 as [H95 H96].
exact H85.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b m c L M B A) as H85.
------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFtransitive (a) (b) (m) (c) (L) (M) (B) (A) (B) (E) (F) (G) (H84) H72).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF a b m c A B M L) as H86.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF a b m c M B A L) /\ ((euclidean__axioms.EF a b m c A B M L) /\ ((euclidean__axioms.EF a b m c B A L M) /\ ((euclidean__axioms.EF a b m c M L A B) /\ ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M))))))) as H86.
-------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (a) (b) (m) (c) (L) (M) (B) (A) H85).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF a b m c M B A L) /\ ((euclidean__axioms.EF a b m c A B M L) /\ ((euclidean__axioms.EF a b m c B A L M) /\ ((euclidean__axioms.EF a b m c M L A B) /\ ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M))))))) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.EF a b m c A B M L) /\ ((euclidean__axioms.EF a b m c B A L M) /\ ((euclidean__axioms.EF a b m c M L A B) /\ ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M)))))) as H89.
---------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.EF a b m c B A L M) /\ ((euclidean__axioms.EF a b m c M L A B) /\ ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M))))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.EF a b m c M L A B) /\ ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M)))) as H93.
------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.EF a b m c A L M B) /\ ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M))) as H95.
------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.EF a b m c B M L A) /\ (euclidean__axioms.EF a b m c L A B M)) as H97.
-------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H89.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E A) as H87.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))))) as H87.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (B) (A) H79).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))))) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E)))) as H90.
----------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))) as H92.
------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------ destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E)) as H94.
------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H88.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R G B A) as H88.
--------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (B) (E) (A) (R) (G) (H63) (H87) H30).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R G A B) as H89.
---------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (B) (A) (R) (G) H88).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS R A B M) as H90.
----------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (A) (B) (R) (G) (M) (H89) H83).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS M A B R) as H91.
------------------------------------------------------------------------------ apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (A) (B) (R) (M) H90).
------------------------------------------------------------------------------ exists M.
exists L.
exists m.
split.
------------------------------------------------------------------------------- exact H68.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H10.
---------------------------------------------------------------------------------- exact H91.
Qed.
