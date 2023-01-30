Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__droppedperpendicularunique.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesideflip.
Require Export lemma__paralleldef2B.
Require Export lemma__planeseparation.
Require Export lemma__squareflip.
Require Export lemma__squareparallelogram.
Require Export logic.
Require Export proposition__47B.
Definition proposition__47 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Per B A C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.SQ A C K H) -> ((euclidean__axioms.TS H C A B) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.TS D C B A) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__defs.PG B X Y D) /\ ((euclidean__axioms.BetS B X C) /\ ((euclidean__defs.PG X C E Y) /\ ((euclidean__axioms.BetS D Y E) /\ ((euclidean__axioms.EF A B F G B X Y D) /\ (euclidean__axioms.EF A C K H X C E Y))))))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro K.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
assert (* Cut *) (exists (M: euclidean__axioms.Point) (L: euclidean__axioms.Point), (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D))))))) as H8.
- apply (@proposition__47B.proposition__47B (A) (B) (C) (D) (E) (F) (G) (H0) (H1) (H2) (H3) (H6) H7).
- assert (exists M: euclidean__axioms.Point, (exists (L: euclidean__axioms.Point), (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D)))))))) as H9.
-- exact H8.
-- destruct H9 as [M H9].
assert (exists L: euclidean__axioms.Point, ((euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D)))))))) as H10.
--- exact H9.
--- destruct H10 as [L H10].
assert (* AndElim *) ((euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D))))))) as H11.
---- exact H10.
---- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D)))))) as H13.
----- exact H12.
----- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D))))) as H15.
------ exact H14.
------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D)))) as H17.
------- exact H16.
------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D))) as H19.
-------- exact H18.
-------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D)) as H21.
--------- exact H20.
--------- destruct H21 as [H21 H22].
assert (* Cut *) (euclidean__axioms.nCol A B C) as H23.
---------- exact H0.
---------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H24.
----------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H24.
------------ apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H23).
------------ assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H25.
------------- exact H24.
------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H27.
-------------- exact H26.
-------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H29.
--------------- exact H28.
--------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H31.
---------------- exact H30.
---------------- destruct H31 as [H31 H32].
exact H31.
----------- assert (* Cut *) (euclidean__axioms.Triangle A C B) as H25.
------------ exact H24.
------------ assert (* Cut *) (euclidean__defs.Per C A B) as H26.
------------- apply (@lemma__8__2.lemma__8__2 (B) (A) (C) H1).
------------- assert (* Cut *) (euclidean__defs.SQ C B D E) as H27.
-------------- apply (@lemma__squareflip.lemma__squareflip (B) (C) (E) (D) H6).
-------------- assert (* Cut *) (euclidean__axioms.TS D B C A) as H28.
--------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip (C) (B) (D) (A) H7).
--------------- assert (* Cut *) (euclidean__defs.PG B C E D) as H29.
---------------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (B) (C) (E) (D) H6).
---------------- assert (* Cut *) (euclidean__defs.Par B C E D) as H30.
----------------- assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H30.
------------------ exact H29.
------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ (euclidean__defs.Par M L C E)) as H32.
------------------- exact H15.
------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H34.
-------------------- exact H11.
-------------------- destruct H34 as [H34 H35].
exact H30.
----------------- assert (* Cut *) (euclidean__defs.TP B C E D) as H31.
------------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B (B) (C) (E) (D) H30).
------------------ assert (* Cut *) (euclidean__defs.OS E D B C) as H32.
------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((~(euclidean__defs.Meet B C E D)) /\ (euclidean__defs.OS E D B C)))) as H32.
-------------------- exact H31.
-------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((~(euclidean__defs.Meet B C E D)) /\ (euclidean__defs.OS E D B C))) as H34.
--------------------- exact H33.
--------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((~(euclidean__defs.Meet B C E D)) /\ (euclidean__defs.OS E D B C)) as H36.
---------------------- exact H35.
---------------------- destruct H36 as [H36 H37].
exact H37.
------------------- assert (* Cut *) (euclidean__axioms.TS E B C A) as H33.
-------------------- apply (@lemma__planeseparation.lemma__planeseparation (B) (C) (E) (D) (A) (H32) H28).
-------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point) (l: euclidean__axioms.Point), (euclidean__defs.PG C m l E) /\ ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E))))))) as H34.
--------------------- apply (@proposition__47B.proposition__47B (A) (C) (B) (E) (D) (K) (H) (H25) (H26) (H4) (H5) (H27) H33).
--------------------- assert (exists m: euclidean__axioms.Point, (exists (l: euclidean__axioms.Point), (euclidean__defs.PG C m l E) /\ ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E)))))))) as H35.
---------------------- exact H34.
---------------------- destruct H35 as [m H35].
assert (exists l: euclidean__axioms.Point, ((euclidean__defs.PG C m l E) /\ ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E)))))))) as H36.
----------------------- exact H35.
----------------------- destruct H36 as [l H36].
assert (* AndElim *) ((euclidean__defs.PG C m l E) /\ ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E))))))) as H37.
------------------------ exact H36.
------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E)))))) as H39.
------------------------- exact H38.
------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E))))) as H41.
-------------------------- exact H40.
-------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E)))) as H43.
--------------------------- exact H42.
--------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E))) as H45.
---------------------------- exact H44.
---------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E)) as H47.
----------------------------- exact H46.
----------------------------- destruct H47 as [H47 H48].
assert (* Cut *) (euclidean__axioms.neq E D) as H49.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq l D) /\ ((euclidean__axioms.neq E l) /\ (euclidean__axioms.neq E D))) as H49.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (l) (D) H43).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq l D) /\ ((euclidean__axioms.neq E l) /\ (euclidean__axioms.neq E D))) as H50.
-------------------------------- exact H49.
-------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq E l) /\ (euclidean__axioms.neq E D)) as H52.
--------------------------------- exact H51.
--------------------------------- destruct H52 as [H52 H53].
exact H53.
------------------------------ assert (* Cut *) (euclidean__axioms.neq D E) as H50.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (D) H49).
------------------------------- assert (* Cut *) (euclidean__axioms.Col E l D) as H51.
-------------------------------- right.
right.
right.
right.
left.
exact H43.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col D L E) as H52.
--------------------------------- right.
right.
right.
right.
left.
exact H17.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col D E L) as H53.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D))))) as H53.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (L) (E) H52).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D))))) as H54.
------------------------------------ exact H53.
------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D)))) as H56.
------------------------------------- exact H55.
------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D))) as H58.
-------------------------------------- exact H57.
-------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D)) as H60.
--------------------------------------- exact H59.
--------------------------------------- destruct H60 as [H60 H61].
exact H60.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D E l) as H54.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col l E D) /\ ((euclidean__axioms.Col l D E) /\ ((euclidean__axioms.Col D E l) /\ ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E))))) as H54.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (l) (D) H51).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col l E D) /\ ((euclidean__axioms.Col l D E) /\ ((euclidean__axioms.Col D E l) /\ ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E))))) as H55.
------------------------------------- exact H54.
------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col l D E) /\ ((euclidean__axioms.Col D E l) /\ ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E)))) as H57.
-------------------------------------- exact H56.
-------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col D E l) /\ ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E))) as H59.
--------------------------------------- exact H58.
--------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E)) as H61.
---------------------------------------- exact H60.
---------------------------------------- destruct H61 as [H61 H62].
exact H59.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col E l L) as H55.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (E) (l) (L)).
-------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False (E) (l) (L) (H55)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (E) (l) (L) (H54) (H53) H50).


------------------------------------ assert (* Cut *) (euclidean__axioms.neq L E) as H56.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.neq D L) /\ (euclidean__axioms.neq D E))) as H56.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (L) (E) H17).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.neq D L) /\ (euclidean__axioms.neq D E))) as H57.
--------------------------------------- exact H56.
--------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq D L) /\ (euclidean__axioms.neq D E)) as H59.
---------------------------------------- exact H58.
---------------------------------------- destruct H59 as [H59 H60].
exact H57.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq E L) as H57.
-------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (L) (E) H56).
-------------------------------------- assert (* Cut *) (euclidean__defs.Per E L A) as H58.
--------------------------------------- apply (@lemma__collinearright.lemma__collinearright (D) (L) (E) (A) (H21) (H52) H57).
--------------------------------------- assert (* Cut *) (l = L) as H59.
---------------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (E) (L) (l) (A) (H47) (H58) H55).
---------------------------------------- assert (* Cut *) (L = l) as H60.
----------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (L) (l) H59).
----------------------------------------- assert (* Cut *) (euclidean__axioms.BetS L m A) as H61.
------------------------------------------ apply (@eq__ind euclidean__axioms.Point l (fun L0: euclidean__axioms.Point => (euclidean__defs.PG B M L0 D) -> ((euclidean__defs.PG M C E L0) -> ((euclidean__axioms.BetS D L0 E) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__axioms.EF A B F G B M L0 D) -> ((euclidean__axioms.Col D L0 E) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__axioms.Col E l L0) -> ((euclidean__axioms.neq L0 E) -> ((euclidean__axioms.neq E L0) -> ((euclidean__defs.Per E L0 A) -> ((L0 = l) -> (euclidean__axioms.BetS L0 m A))))))))))))))) with (y := L).
-------------------------------------------intro H61.
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
assert (* Cut *) (l = l) as H74.
-------------------------------------------- exact H73.
-------------------------------------------- exact H45.

------------------------------------------- exact H59.
------------------------------------------- exact H11.
------------------------------------------- exact H15.
------------------------------------------- exact H17.
------------------------------------------- exact H19.
------------------------------------------- exact H21.
------------------------------------------- exact H22.
------------------------------------------- exact H52.
------------------------------------------- exact H53.
------------------------------------------- exact H55.
------------------------------------------- exact H56.
------------------------------------------- exact H57.
------------------------------------------- exact H58.
------------------------------------------- exact H60.
------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS C M B) as H62.
------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (C) H13).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L m A) as H63.
-------------------------------------------- right.
right.
right.
right.
left.
exact H61.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L M A) as H64.
--------------------------------------------- right.
right.
right.
right.
left.
exact H19.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L A m) as H65.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m L A) /\ ((euclidean__axioms.Col m A L) /\ ((euclidean__axioms.Col A L m) /\ ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L))))) as H65.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (L) (m) (A) H63).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m L A) /\ ((euclidean__axioms.Col m A L) /\ ((euclidean__axioms.Col A L m) /\ ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L))))) as H66.
------------------------------------------------ exact H65.
------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col m A L) /\ ((euclidean__axioms.Col A L m) /\ ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L)))) as H68.
------------------------------------------------- exact H67.
------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col A L m) /\ ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L))) as H70.
-------------------------------------------------- exact H69.
-------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L)) as H72.
--------------------------------------------------- exact H71.
--------------------------------------------------- destruct H72 as [H72 H73].
exact H72.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L A M) as H66.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H66.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (L) (M) (A) H64).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H67.
------------------------------------------------- exact H66.
------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L)))) as H69.
-------------------------------------------------- exact H68.
-------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))) as H71.
--------------------------------------------------- exact H70.
--------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L)) as H73.
---------------------------------------------------- exact H72.
---------------------------------------------------- destruct H73 as [H73 H74].
exact H73.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L A) as H67.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq L m) /\ (euclidean__axioms.neq L A))) as H67.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (L) (m) (A) H61).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq L m) /\ (euclidean__axioms.neq L A))) as H68.
-------------------------------------------------- exact H67.
-------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq L m) /\ (euclidean__axioms.neq L A)) as H70.
--------------------------------------------------- exact H69.
--------------------------------------------------- destruct H70 as [H70 H71].
exact H71.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A m M) as H68.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (m) (M)).
--------------------------------------------------intro H68.
apply (@euclidean__tactics.Col__nCol__False (A) (m) (M) (H68)).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (L) (A) (m) (M) (H65) (H66) H67).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M m A) as H69.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col M A m) /\ ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A))))) as H69.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (m) (M) H68).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col M A m) /\ ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A))))) as H70.
---------------------------------------------------- exact H69.
---------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col M A m) /\ ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A)))) as H72.
----------------------------------------------------- exact H71.
----------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col M A m) /\ ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A))) as H74.
------------------------------------------------------ exact H73.
------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A)) as H76.
------------------------------------------------------- exact H75.
------------------------------------------------------- destruct H76 as [H76 H77].
exact H77.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M C) as H70.
--------------------------------------------------- right.
right.
right.
right.
left.
exact H13.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H71.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H71.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (C) H70).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H72.
------------------------------------------------------ exact H71.
------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)))) as H74.
------------------------------------------------------- exact H73.
------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))) as H76.
-------------------------------------------------------- exact H75.
-------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)) as H78.
--------------------------------------------------------- exact H77.
--------------------------------------------------------- destruct H78 as [H78 H79].
exact H76.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C m B) as H72.
----------------------------------------------------- right.
right.
right.
right.
left.
exact H39.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B m) as H73.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col B C m) /\ ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C))))) as H73.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (m) (B) H72).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col B C m) /\ ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C))))) as H74.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col B C m) /\ ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C)))) as H76.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col B C m) /\ ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C))) as H78.
---------------------------------------------------------- exact H77.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C)) as H80.
----------------------------------------------------------- exact H79.
----------------------------------------------------------- destruct H80 as [H80 H81].
exact H80.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H74.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H74.
-------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (M) (B) H62).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H75.
--------------------------------------------------------- exact H74.
--------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B)) as H77.
---------------------------------------------------------- exact H76.
---------------------------------------------------------- destruct H77 as [H77 H78].
exact H78.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M m) as H75.
-------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (M) (m)).
---------------------------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False (B) (M) (m) (H75)).
----------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (M) (m) (H71) (H73) H74).


-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M m B) as H76.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B m) /\ ((euclidean__axioms.Col M m B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B))))) as H76.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (m) H75).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B m) /\ ((euclidean__axioms.Col M m B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B))))) as H77.
----------------------------------------------------------- exact H76.
----------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col M m B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B)))) as H79.
------------------------------------------------------------ exact H78.
------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B))) as H81.
------------------------------------------------------------- exact H80.
------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B)) as H83.
-------------------------------------------------------------- exact H82.
-------------------------------------------------------------- destruct H83 as [H83 H84].
exact H79.
--------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq M m)) as H77.
---------------------------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col m M A) as H78.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col A M m) /\ ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M))))) as H78.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (M) (m) (A) H69).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col A M m) /\ ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M))))) as H79.
------------------------------------------------------------- exact H78.
------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col A M m) /\ ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M)))) as H81.
-------------------------------------------------------------- exact H80.
-------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col A M m) /\ ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M))) as H83.
--------------------------------------------------------------- exact H82.
--------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M)) as H85.
---------------------------------------------------------------- exact H84.
---------------------------------------------------------------- destruct H85 as [H85 H86].
exact H79.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m M B) as H79.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m M B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B M m) /\ ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M))))) as H79.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (M) (m) (B) H76).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m M B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B M m) /\ ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M))))) as H80.
-------------------------------------------------------------- exact H79.
-------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B M m) /\ ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M)))) as H82.
--------------------------------------------------------------- exact H81.
--------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B M m) /\ ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M))) as H84.
---------------------------------------------------------------- exact H83.
---------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M)) as H86.
----------------------------------------------------------------- exact H85.
----------------------------------------------------------------- destruct H86 as [H86 H87].
exact H80.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq m M) as H80.
------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (M) (m) H77).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A B) as H81.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (M) (A) (B)).
---------------------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False (M) (A) (B) (H81)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (m) (M) (A) (B) (H78) (H79) H80).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B A) as H82.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A M B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M))))) as H82.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (M) (A) (B) H81).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A M B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M))))) as H83.
----------------------------------------------------------------- exact H82.
----------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M)))) as H85.
------------------------------------------------------------------ exact H84.
------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M))) as H87.
------------------------------------------------------------------- exact H86.
------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M)) as H89.
-------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H89.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B C) as H83.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H83.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (M) H71).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H84.
------------------------------------------------------------------ exact H83.
------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)))) as H86.
------------------------------------------------------------------- exact H85.
------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))) as H88.
-------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)) as H90.
--------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H91.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M B) as H84.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H84.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (M) (B) H62).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H85.
------------------------------------------------------------------- exact H84.
------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B)) as H87.
-------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H85.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H85.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------------------------------------------------------------------intro H85.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H85)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (B) (A) (C) (H82) (H83) H84).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H86.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H86.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H85).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H87.
--------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H89.
---------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H91.
----------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H93.
------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------ destruct H93 as [H93 H94].
exact H87.
------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (B) (H25)).
--------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (B)).
---------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H23) H86).


---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H C M l E) as H78.
----------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point m (fun X: euclidean__axioms.Point => euclidean__axioms.EF A C K H C X l E)) with (x := M).
------------------------------------------------------------ exact H48.
------------------------------------------------------------apply (@euclidean__tactics.NNPP (M = m) H77).

----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H C M L E) as H79.
------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point l (fun L0: euclidean__axioms.Point => (euclidean__defs.PG B M L0 D) -> ((euclidean__defs.PG M C E L0) -> ((euclidean__axioms.BetS D L0 E) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__axioms.EF A B F G B M L0 D) -> ((euclidean__axioms.Col D L0 E) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__axioms.Col E l L0) -> ((euclidean__axioms.neq L0 E) -> ((euclidean__axioms.neq E L0) -> ((euclidean__defs.Per E L0 A) -> ((L0 = l) -> ((euclidean__axioms.BetS L0 m A) -> ((euclidean__axioms.Col L0 m A) -> ((euclidean__axioms.Col L0 M A) -> ((euclidean__axioms.Col L0 A m) -> ((euclidean__axioms.Col L0 A M) -> ((euclidean__axioms.neq L0 A) -> (euclidean__axioms.EF A C K H C M L0 E))))))))))))))))))))) with (y := L).
-------------------------------------------------------------intro H79.
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
assert (* Cut *) (l = l) as H98.
-------------------------------------------------------------- exact H91.
-------------------------------------------------------------- exact H78.

------------------------------------------------------------- exact H59.
------------------------------------------------------------- exact H11.
------------------------------------------------------------- exact H15.
------------------------------------------------------------- exact H17.
------------------------------------------------------------- exact H19.
------------------------------------------------------------- exact H21.
------------------------------------------------------------- exact H22.
------------------------------------------------------------- exact H52.
------------------------------------------------------------- exact H53.
------------------------------------------------------------- exact H55.
------------------------------------------------------------- exact H56.
------------------------------------------------------------- exact H57.
------------------------------------------------------------- exact H58.
------------------------------------------------------------- exact H60.
------------------------------------------------------------- exact H61.
------------------------------------------------------------- exact H63.
------------------------------------------------------------- exact H64.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- exact H67.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A C K H M C E L) as H80.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF A C K H M L E C) /\ ((euclidean__axioms.EF A C K H E L M C) /\ ((euclidean__axioms.EF A C K H L E C M) /\ ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M))))))) as H80.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (A) (C) (K) (H) (C) (M) (L) (E) H79).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF A C K H M L E C) /\ ((euclidean__axioms.EF A C K H E L M C) /\ ((euclidean__axioms.EF A C K H L E C M) /\ ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M))))))) as H81.
--------------------------------------------------------------- exact H80.
--------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.EF A C K H E L M C) /\ ((euclidean__axioms.EF A C K H L E C M) /\ ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M)))))) as H83.
---------------------------------------------------------------- exact H82.
---------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.EF A C K H L E C M) /\ ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M))))) as H85.
----------------------------------------------------------------- exact H84.
----------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M)))) as H87.
------------------------------------------------------------------ exact H86.
------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M))) as H89.
------------------------------------------------------------------- exact H88.
------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M)) as H91.
-------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H87.
------------------------------------------------------------- exists M.
exists L.
split.
-------------------------------------------------------------- exact H11.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H13.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H15.
---------------------------------------------------------------- split.
----------------------------------------------------------------- exact H17.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H22.
------------------------------------------------------------------ exact H80.
Qed.
