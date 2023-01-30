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
Definition proposition__47 : forall A B C D E F G H K, (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Per B A C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.SQ A C K H) -> ((euclidean__axioms.TS H C A B) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.TS D C B A) -> (exists X Y, (euclidean__defs.PG B X Y D) /\ ((euclidean__axioms.BetS B X C) /\ ((euclidean__defs.PG X C E Y) /\ ((euclidean__axioms.BetS D Y E) /\ ((euclidean__axioms.EF A B F G B X Y D) /\ (euclidean__axioms.EF A C K H X C E Y))))))))))))).
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
assert (* Cut *) (exists M L, (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ ((euclidean__defs.Per D L A) /\ (euclidean__axioms.EF A B F G B M L D))))))) as H8.
- apply (@proposition__47B.proposition__47B A B C D E F G H0 H1 H2 H3 H6 H7).
- destruct H8 as [M H9].
destruct H9 as [L H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (euclidean__axioms.nCol A B C) as H23 by exact H0.
assert (* Cut *) (euclidean__axioms.nCol A C B) as H24.
-- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H24.
--- apply (@lemma__NCorder.lemma__NCorder A B C H23).
--- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
-- assert (euclidean__axioms.Triangle A C B) as H25 by exact H24.
assert (* Cut *) (euclidean__defs.Per C A B) as H26.
--- apply (@lemma__8__2.lemma__8__2 B A C H1).
--- assert (* Cut *) (euclidean__defs.SQ C B D E) as H27.
---- apply (@lemma__squareflip.lemma__squareflip B C E D H6).
---- assert (* Cut *) (euclidean__axioms.TS D B C A) as H28.
----- apply (@lemma__oppositesideflip.lemma__oppositesideflip C B D A H7).
----- assert (* Cut *) (euclidean__defs.PG B C E D) as H29.
------ apply (@lemma__squareparallelogram.lemma__squareparallelogram B C E D H6).
------ assert (* Cut *) (euclidean__defs.Par B C E D) as H30.
------- destruct H29 as [H30 H31].
destruct H15 as [H32 H33].
destruct H11 as [H34 H35].
exact H30.
------- assert (* Cut *) (euclidean__defs.TP B C E D) as H31.
-------- apply (@lemma__paralleldef2B.lemma__paralleldef2B B C E D H30).
-------- assert (* Cut *) (euclidean__defs.OS E D B C) as H32.
--------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H37.
--------- assert (* Cut *) (euclidean__axioms.TS E B C A) as H33.
---------- apply (@lemma__planeseparation.lemma__planeseparation B C E D A H32 H28).
---------- assert (* Cut *) (exists m l, (euclidean__defs.PG C m l E) /\ ((euclidean__axioms.BetS C m B) /\ ((euclidean__defs.PG m B D l) /\ ((euclidean__axioms.BetS E l D) /\ ((euclidean__axioms.BetS l m A) /\ ((euclidean__defs.Per E l A) /\ (euclidean__axioms.EF A C K H C m l E))))))) as H34.
----------- apply (@proposition__47B.proposition__47B A C B E D K H H25 H26 H4 H5 H27 H33).
----------- destruct H34 as [m H35].
destruct H35 as [l H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
assert (* Cut *) (euclidean__axioms.neq E D) as H49.
------------ assert (* Cut *) ((euclidean__axioms.neq l D) /\ ((euclidean__axioms.neq E l) /\ (euclidean__axioms.neq E D))) as H49.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal E l D H43).
------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
------------ assert (* Cut *) (euclidean__axioms.neq D E) as H50.
------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E D H49).
------------- assert (* Cut *) (euclidean__axioms.Col E l D) as H51.
-------------- right.
right.
right.
right.
left.
exact H43.
-------------- assert (* Cut *) (euclidean__axioms.Col D L E) as H52.
--------------- right.
right.
right.
right.
left.
exact H17.
--------------- assert (* Cut *) (euclidean__axioms.Col D E L) as H53.
---------------- assert (* Cut *) ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col D E L) /\ (euclidean__axioms.Col E L D))))) as H53.
----------------- apply (@lemma__collinearorder.lemma__collinearorder D L E H52).
----------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H60.
---------------- assert (* Cut *) (euclidean__axioms.Col D E l) as H54.
----------------- assert (* Cut *) ((euclidean__axioms.Col l E D) /\ ((euclidean__axioms.Col l D E) /\ ((euclidean__axioms.Col D E l) /\ ((euclidean__axioms.Col E D l) /\ (euclidean__axioms.Col D l E))))) as H54.
------------------ apply (@lemma__collinearorder.lemma__collinearorder E l D H51).
------------------ destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H59.
----------------- assert (* Cut *) (euclidean__axioms.Col E l L) as H55.
------------------ apply (@euclidean__tactics.not__nCol__Col E l L).
-------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False E l L H55).
--------------------apply (@lemma__collinear4.lemma__collinear4 D E l L H54 H53 H50).


------------------ assert (* Cut *) (euclidean__axioms.neq L E) as H56.
------------------- assert (* Cut *) ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.neq D L) /\ (euclidean__axioms.neq D E))) as H56.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D L E H17).
-------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H57.
------------------- assert (* Cut *) (euclidean__axioms.neq E L) as H57.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric L E H56).
-------------------- assert (* Cut *) (euclidean__defs.Per E L A) as H58.
--------------------- apply (@lemma__collinearright.lemma__collinearright D L E A H21 H52 H57).
--------------------- assert (* Cut *) (l = L) as H59.
---------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique E L l A H47 H58 H55).
---------------------- assert (* Cut *) (L = l) as H60.
----------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric L l H59).
----------------------- assert (* Cut *) (euclidean__axioms.BetS L m A) as H61.
------------------------ apply (@eq__ind euclidean__axioms.Point l (fun L0 => (euclidean__defs.PG B M L0 D) -> ((euclidean__defs.PG M C E L0) -> ((euclidean__axioms.BetS D L0 E) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__axioms.EF A B F G B M L0 D) -> ((euclidean__axioms.Col D L0 E) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__axioms.Col E l L0) -> ((euclidean__axioms.neq L0 E) -> ((euclidean__axioms.neq E L0) -> ((euclidean__defs.Per E L0 A) -> ((L0 = l) -> (euclidean__axioms.BetS L0 m A))))))))))))))) with (y := L).
-------------------------intro H61.
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
assert (l = l) as H74 by exact H73.
exact H45.

------------------------- exact H59.
------------------------- exact H11.
------------------------- exact H15.
------------------------- exact H17.
------------------------- exact H19.
------------------------- exact H21.
------------------------- exact H22.
------------------------- exact H52.
------------------------- exact H53.
------------------------- exact H55.
------------------------- exact H56.
------------------------- exact H57.
------------------------- exact H58.
------------------------- exact H60.
------------------------ assert (* Cut *) (euclidean__axioms.BetS C M B) as H62.
------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B M C H13).
------------------------- assert (* Cut *) (euclidean__axioms.Col L m A) as H63.
-------------------------- right.
right.
right.
right.
left.
exact H61.
-------------------------- assert (* Cut *) (euclidean__axioms.Col L M A) as H64.
--------------------------- right.
right.
right.
right.
left.
exact H19.
--------------------------- assert (* Cut *) (euclidean__axioms.Col L A m) as H65.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col m L A) /\ ((euclidean__axioms.Col m A L) /\ ((euclidean__axioms.Col A L m) /\ ((euclidean__axioms.Col L A m) /\ (euclidean__axioms.Col A m L))))) as H65.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder L m A H63).
----------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H72.
---------------------------- assert (* Cut *) (euclidean__axioms.Col L A M) as H66.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H66.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder L M A H64).
------------------------------ destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
----------------------------- assert (* Cut *) (euclidean__axioms.neq L A) as H67.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq L m) /\ (euclidean__axioms.neq L A))) as H67.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L m A H61).
------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H71.
------------------------------ assert (* Cut *) (euclidean__axioms.Col A m M) as H68.
------------------------------- apply (@euclidean__tactics.not__nCol__Col A m M).
--------------------------------intro H68.
apply (@euclidean__tactics.Col__nCol__False A m M H68).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 L A m M H65 H66 H67).


------------------------------- assert (* Cut *) (euclidean__axioms.Col M m A) as H69.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col M A m) /\ ((euclidean__axioms.Col A M m) /\ (euclidean__axioms.Col M m A))))) as H69.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A m M H68).
--------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H77.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B M C) as H70.
--------------------------------- right.
right.
right.
right.
left.
exact H13.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H71.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H71.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M C H70).
----------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H76.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col C m B) as H72.
----------------------------------- right.
right.
right.
right.
left.
exact H39.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col C B m) as H73.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col B C m) /\ ((euclidean__axioms.Col C B m) /\ (euclidean__axioms.Col B m C))))) as H73.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C m B H72).
------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H80.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H74.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H74.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M B H62).
-------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M m) as H75.
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col B M m).
---------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False B M m H75).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 C B M m H71 H73 H74).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col M m B) as H76.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B m) /\ ((euclidean__axioms.Col M m B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B m M) /\ (euclidean__axioms.Col m M B))))) as H76.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M m H75).
---------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H79.
--------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq M m)) as H77.
---------------------------------------- intro H77.
assert (* Cut *) (euclidean__axioms.Col m M A) as H78.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m M A) /\ ((euclidean__axioms.Col m A M) /\ ((euclidean__axioms.Col A M m) /\ ((euclidean__axioms.Col M A m) /\ (euclidean__axioms.Col A m M))))) as H78.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder M m A H69).
------------------------------------------ destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H79.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col m M B) as H79.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m M B) /\ ((euclidean__axioms.Col m B M) /\ ((euclidean__axioms.Col B M m) /\ ((euclidean__axioms.Col M B m) /\ (euclidean__axioms.Col B m M))))) as H79.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder M m B H76).
------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H80.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq m M) as H80.
------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M m H77).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A B) as H81.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col M A B).
---------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False M A B H81).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 m M A B H78 H79 H80).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B A) as H82.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A M B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M B A) /\ (euclidean__axioms.Col B A M))))) as H82.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder M A B H81).
---------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H89.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B C) as H83.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H83.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B M H71).
----------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H91.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M B) as H84.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H84.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C M B H62).
------------------------------------------------ destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H85.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H85.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col B A C).
-------------------------------------------------intro H85.
apply (@euclidean__tactics.Col__nCol__False B A C H85).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 M B A C H82 H83 H84).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H86.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H86.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H85).
-------------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
exact H87.
------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False A C B H25).
--------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A C B).
---------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False A B C H23 H86).


---------------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H C M l E) as H78.
----------------------------------------- apply (@eq__ind__r euclidean__axioms.Point m (fun X => euclidean__axioms.EF A C K H C X l E)) with (x := M).
------------------------------------------ exact H48.
------------------------------------------apply (@euclidean__tactics.NNPP (M = m) H77).

----------------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H C M L E) as H79.
------------------------------------------ apply (@eq__ind euclidean__axioms.Point l (fun L0 => (euclidean__defs.PG B M L0 D) -> ((euclidean__defs.PG M C E L0) -> ((euclidean__axioms.BetS D L0 E) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__axioms.EF A B F G B M L0 D) -> ((euclidean__axioms.Col D L0 E) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__axioms.Col E l L0) -> ((euclidean__axioms.neq L0 E) -> ((euclidean__axioms.neq E L0) -> ((euclidean__defs.Per E L0 A) -> ((L0 = l) -> ((euclidean__axioms.BetS L0 m A) -> ((euclidean__axioms.Col L0 m A) -> ((euclidean__axioms.Col L0 M A) -> ((euclidean__axioms.Col L0 A m) -> ((euclidean__axioms.Col L0 A M) -> ((euclidean__axioms.neq L0 A) -> (euclidean__axioms.EF A C K H C M L0 E))))))))))))))))))))) with (y := L).
-------------------------------------------intro H79.
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
assert (l = l) as H98 by exact H91.
exact H78.

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
------------------------------------------- exact H61.
------------------------------------------- exact H63.
------------------------------------------- exact H64.
------------------------------------------- exact H65.
------------------------------------------- exact H66.
------------------------------------------- exact H67.
------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A C K H M C E L) as H80.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF A C K H M L E C) /\ ((euclidean__axioms.EF A C K H E L M C) /\ ((euclidean__axioms.EF A C K H L E C M) /\ ((euclidean__axioms.EF A C K H M C E L) /\ ((euclidean__axioms.EF A C K H E C M L) /\ ((euclidean__axioms.EF A C K H L M C E) /\ (euclidean__axioms.EF A C K H C E L M))))))) as H80.
-------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation A C K H C M L E H79).
-------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H87.
------------------------------------------- exists M.
exists L.
split.
-------------------------------------------- exact H11.
-------------------------------------------- split.
--------------------------------------------- exact H13.
--------------------------------------------- split.
---------------------------------------------- exact H15.
---------------------------------------------- split.
----------------------------------------------- exact H17.
----------------------------------------------- split.
------------------------------------------------ exact H22.
------------------------------------------------ exact H80.
Qed.
