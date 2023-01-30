Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__angledistinct.
Require Export lemma__angletrichotomy.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__ray4.
Require Export lemma__raystrict.
Require Export lemma__trichotomy1.
Require Export logic.
Require Export proposition__04.
Definition proposition__26A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D E F) -> ((euclidean__defs.CongA A B C D E F) -> ((euclidean__defs.CongA B C A E F D) -> ((euclidean__axioms.Cong B C E F) -> ((euclidean__axioms.Cong A B D E) /\ ((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F))))))).
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
assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
- exact H.
- assert (* Cut *) (~(A = B)) as H5.
-- intro H5.
assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
--- left.
exact H5.
--- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H6).
-- assert (* Cut *) (euclidean__axioms.neq B A) as H6.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H5).
--- assert (* Cut *) (~(B = C)) as H7.
---- intro H7.
assert (* Cut *) (euclidean__axioms.Col A B C) as H8.
----- right.
right.
left.
exact H7.
----- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H8).
---- assert (* Cut *) (euclidean__axioms.neq C B) as H8.
----- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H7).
----- assert (* Cut *) (~(A = C)) as H9.
------ intro H9.
assert (* Cut *) (euclidean__axioms.Col A B C) as H10.
------- right.
left.
exact H9.
------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H10).
------ assert (* Cut *) (euclidean__axioms.neq C A) as H10.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H9).
------- assert (* Cut *) (~(euclidean__defs.Lt D E A B)) as H11.
-------- intro H11.
assert (* Cut *) (euclidean__axioms.Cong A B B A) as H12.
--------- apply (@euclidean__axioms.cn__equalityreverse (A) B).
--------- assert (* Cut *) (euclidean__defs.Lt D E B A) as H13.
---------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (D) (E) (A) (B) (B) (A) (H11) H12).
---------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong B G D E)) as H14.
----------- exact H13.
----------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong B G D E))) as H15.
------------ exact H14.
------------ destruct H15 as [G H15].
assert (* AndElim *) ((euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong B G D E)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* Cut *) (euclidean__axioms.neq B G) as H18.
-------------- assert (* Cut *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A))) as H18.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (G) (A) H16).
--------------- assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H21.
-------------- assert (* Cut *) (euclidean__axioms.Cong B G E D) as H19.
--------------- assert (* Cut *) ((euclidean__axioms.Cong G B E D) /\ ((euclidean__axioms.Cong G B D E) /\ (euclidean__axioms.Cong B G E D))) as H19.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (G) (D) (E) H17).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong G B E D) /\ ((euclidean__axioms.Cong G B D E) /\ (euclidean__axioms.Cong B G E D))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong G B D E) /\ (euclidean__axioms.Cong B G E D)) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
exact H23.
--------------- assert (* Cut *) (euclidean__defs.Out B A G) as H20.
---------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (G)).
-----------------left.
exact H16.

----------------- exact H6.
---------------- assert (* Cut *) (C = C) as H21.
----------------- apply (@logic.eq__refl (Point) C).
----------------- assert (* Cut *) (euclidean__defs.Out B C C) as H22.
------------------ apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
-------------------right.
left.
exact H21.

------------------- exact H7.
------------------ assert (* Cut *) (euclidean__axioms.Cong G C G C) as H23.
------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) C).
------------------- assert (* Cut *) (B = B) as H24.
-------------------- apply (@logic.eq__refl (Point) B).
-------------------- assert (* Cut *) (G = G) as H25.
--------------------- apply (@logic.eq__refl (Point) G).
--------------------- assert (* Cut *) (euclidean__defs.Out B G G) as H26.
---------------------- apply (@lemma__ray4.lemma__ray4 (B) (G) (G)).
-----------------------right.
left.
exact H25.

----------------------- exact H18.
---------------------- assert (* Cut *) (euclidean__axioms.Cong B G B G) as H27.
----------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) G).
----------------------- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H28.
------------------------ apply (@euclidean__axioms.cn__congruencereflexive (B) C).
------------------------ assert (* Cut *) (euclidean__defs.CongA A B C G B C) as H29.
------------------------- exists G.
exists C.
exists G.
exists C.
split.
-------------------------- exact H20.
-------------------------- split.
--------------------------- exact H22.
--------------------------- split.
---------------------------- exact H26.
---------------------------- split.
----------------------------- exact H22.
----------------------------- split.
------------------------------ exact H27.
------------------------------ split.
------------------------------- exact H28.
------------------------------- split.
-------------------------------- exact H23.
-------------------------------- exact H4.
------------------------- assert (* Cut *) (euclidean__defs.CongA G B C A B C) as H30.
-------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (G) (B) (C) H29).
-------------------------- assert (* Cut *) (euclidean__defs.CongA G B C D E F) as H31.
--------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (B) (C) (A) (B) (C) (D) (E) (F) (H30) H1).
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H32.
---------------------------- apply (@proposition__04.proposition__04 (B) (G) (C) (E) (D) (F) (H19) (H3) H31).
---------------------------- assert (* Cut *) (euclidean__defs.CongA E F D B C A) as H33.
----------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (A) (E) (F) (D) H2).
----------------------------- assert (* Cut *) (euclidean__defs.CongA B C G B C A) as H34.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H34.
------------------------------- exact H32.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (C) (G) (E) (F) (D) (B) (C) (A) (H37) H33).
------------------------------ assert (* Cut *) (euclidean__defs.CongA B C A B C G) as H35.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H35.
-------------------------------- exact H32.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (G) (B) (C) (A) H34).
------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H36.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H36.
--------------------------------- exact H32.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
-----------------------------------right.
left.
exact H24.

----------------------------------- exact H8.
-------------------------------- assert (* Cut *) (A = A) as H37.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H37.
---------------------------------- exact H32.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
apply (@logic.eq__refl (Point) A).
--------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H38.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H38.
----------------------------------- exact H32.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
-------------------------------------right.
left.
exact H37.

------------------------------------- exact H10.
---------------------------------- assert (* Cut *) (euclidean__defs.LtA B C A B C A) as H39.
----------------------------------- exists B.
exists G.
exists A.
split.
------------------------------------ exact H16.
------------------------------------ split.
------------------------------------- exact H36.
------------------------------------- split.
-------------------------------------- exact H38.
-------------------------------------- exact H35.
----------------------------------- assert (* Cut *) (~(euclidean__defs.LtA B C A B C A)) as H40.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong G C D F) /\ ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D))) as H40.
------------------------------------- exact H32.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.CongA B G C E D F) /\ (euclidean__defs.CongA B C G E F D)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
apply (@lemma__angletrichotomy.lemma__angletrichotomy (B) (C) (A) (B) (C) (A) H39).
------------------------------------ apply (@H40 H39).
-------- assert (* Cut *) (~(euclidean__defs.Lt A B D E)) as H12.
--------- intro H12.
assert (* Cut *) (euclidean__axioms.Cong D E E D) as H13.
---------- apply (@euclidean__axioms.cn__equalityreverse (D) E).
---------- assert (* Cut *) (euclidean__defs.Lt A B E D) as H14.
----------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (A) (B) (D) (E) (E) (D) (H12) H13).
----------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS E G D) /\ (euclidean__axioms.Cong E G A B)) as H15.
------------ exact H14.
------------ assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS E G D) /\ (euclidean__axioms.Cong E G A B))) as H16.
------------- exact H15.
------------- destruct H16 as [G H16].
assert (* AndElim *) ((euclidean__axioms.BetS E G D) /\ (euclidean__axioms.Cong E G A B)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* Cut *) (euclidean__axioms.Cong E G B A) as H19.
--------------- assert (* Cut *) ((euclidean__axioms.Cong G E B A) /\ ((euclidean__axioms.Cong G E A B) /\ (euclidean__axioms.Cong E G B A))) as H19.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (G) (A) (B) H18).
---------------- assert (* AndElim *) ((euclidean__axioms.Cong G E B A) /\ ((euclidean__axioms.Cong G E A B) /\ (euclidean__axioms.Cong E G B A))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong G E A B) /\ (euclidean__axioms.Cong E G B A)) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
exact H23.
--------------- assert (* Cut *) (euclidean__axioms.neq E D) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E D))) as H20.
----------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (D) H17).
----------------- assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E D))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E D)) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
exact H24.
---------------- assert (* Cut *) (euclidean__defs.Out E D G) as H21.
----------------- apply (@lemma__ray4.lemma__ray4 (E) (D) (G)).
------------------left.
exact H17.

------------------ exact H20.
----------------- assert (* Cut *) (D = D) as H22.
------------------ apply (@logic.eq__refl (Point) D).
------------------ assert (* Cut *) (F = F) as H23.
------------------- apply (@logic.eq__refl (Point) F).
------------------- assert (* Cut *) (euclidean__axioms.nCol D E F) as H24.
-------------------- exact H0.
-------------------- assert (* Cut *) (~(E = F)) as H25.
--------------------- intro H25.
assert (* Cut *) (euclidean__axioms.Col D E F) as H26.
---------------------- right.
right.
left.
exact H25.
---------------------- apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H24) H26).
--------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H26.
---------------------- apply (@lemma__ray4.lemma__ray4 (E) (F) (F)).
-----------------------right.
left.
exact H23.

----------------------- exact H25.
---------------------- assert (* Cut *) (euclidean__axioms.Cong G F G F) as H27.
----------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) F).
----------------------- assert (* Cut *) (E = E) as H28.
------------------------ apply (@logic.eq__refl (Point) E).
------------------------ assert (* Cut *) (G = G) as H29.
------------------------- apply (@logic.eq__refl (Point) G).
------------------------- assert (* Cut *) (euclidean__axioms.neq E G) as H30.
-------------------------- apply (@lemma__raystrict.lemma__raystrict (E) (D) (G) H21).
-------------------------- assert (* Cut *) (euclidean__defs.Out E G G) as H31.
--------------------------- apply (@lemma__ray4.lemma__ray4 (E) (G) (G)).
----------------------------right.
left.
exact H29.

---------------------------- exact H30.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong E G E G) as H32.
---------------------------- apply (@euclidean__axioms.cn__congruencereflexive (E) G).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong E F E F) as H33.
----------------------------- apply (@euclidean__axioms.cn__congruencereflexive (E) F).
----------------------------- assert (* Cut *) (euclidean__defs.CongA D E F G E F) as H34.
------------------------------ exists G.
exists F.
exists G.
exists F.
split.
------------------------------- exact H21.
------------------------------- split.
-------------------------------- exact H26.
-------------------------------- split.
--------------------------------- exact H31.
--------------------------------- split.
---------------------------------- exact H26.
---------------------------------- split.
----------------------------------- exact H32.
----------------------------------- split.
------------------------------------ exact H33.
------------------------------------ split.
------------------------------------- exact H27.
------------------------------------- exact H24.
------------------------------ assert (* Cut *) (euclidean__defs.CongA G E F D E F) as H35.
------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (G) (E) (F) H34).
------------------------------- assert (* Cut *) (euclidean__defs.CongA D E F A B C) as H36.
-------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (D) (E) (F) H1).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F A B C) as H37.
--------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (E) (F) (D) (E) (F) (A) (B) (C) (H35) H36).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F B C) as H38.
---------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (B) (C) (F) H3).
---------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H39.
----------------------------------- apply (@proposition__04.proposition__04 (E) (G) (F) (B) (A) (C) (H19) (H38) H37).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA E F G E F D) as H40.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (E) (F) (G) (B) (C) (A) (E) (F) (D) (H43) H2).
------------------------------------ assert (* Cut *) (euclidean__defs.CongA E F D E F G) as H41.
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H41.
-------------------------------------- exact H39.
-------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (E) (F) (G) (E) (F) (D) H40).
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E F G) as H42.
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H42.
--------------------------------------- exact H39.
--------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [H44 H45].
apply (@euclidean__tactics.nCol__notCol (E) (F) (G)).
-----------------------------------------apply (@euclidean__tactics.nCol__not__Col (E) (F) (G)).
------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (E) (F) (D) (E) (F) (G) H41).


-------------------------------------- assert (* Cut *) (euclidean__defs.CongA E F G E F G) as H43.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H43.
---------------------------------------- exact H39.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (E) (F) (G) H42).
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H44.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H44.
----------------------------------------- exact H39.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))))) as H48.
------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (E) (F) (G) (E) (F) (G) H43).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G))))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G))) as H55.
----------------------------------------------- exact H54.
----------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
exact H55.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H45.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H45.
------------------------------------------ exact H39.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H44).
----------------------------------------- assert (* Cut *) (euclidean__defs.Out F E E) as H46.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H46.
------------------------------------------- exact H39.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
apply (@lemma__ray4.lemma__ray4 (F) (E) (E)).
---------------------------------------------right.
left.
exact H28.

--------------------------------------------- exact H45.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F D) as H47.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H47.
-------------------------------------------- exact H39.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))))) as H51.
---------------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct (E) (F) (D) (E) (F) (G) H41).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))))) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G))))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)))) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G))) as H58.
-------------------------------------------------- exact H57.
-------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq E G)) as H60.
--------------------------------------------------- exact H59.
--------------------------------------------------- destruct H60 as [H60 H61].
exact H54.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out F D D) as H48.
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H48.
--------------------------------------------- exact H39.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
apply (@lemma__ray4.lemma__ray4 (F) (D) (D)).
-----------------------------------------------right.
left.
exact H22.

----------------------------------------------- exact H47.
-------------------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D E F D) as H49.
--------------------------------------------- exists E.
exists G.
exists D.
split.
---------------------------------------------- exact H17.
---------------------------------------------- split.
----------------------------------------------- exact H46.
----------------------------------------------- split.
------------------------------------------------ exact H48.
------------------------------------------------ exact H41.
--------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA E F D E F D)) as H50.
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong G F A C) /\ ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A))) as H50.
----------------------------------------------- exact H39.
----------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.CongA E G F B A C) /\ (euclidean__defs.CongA E F G B C A)) as H52.
------------------------------------------------ exact H51.
------------------------------------------------ destruct H52 as [H52 H53].
apply (@lemma__angletrichotomy.lemma__angletrichotomy (E) (F) (D) (E) (F) (D) H49).
---------------------------------------------- apply (@H50 H49).
--------- assert (* Cut *) (~(D = E)) as H13.
---------- intro H13.
assert (* Cut *) (euclidean__axioms.Col D E F) as H14.
----------- left.
exact H13.
----------- assert (* Cut *) (euclidean__axioms.nCol D E F) as H15.
------------ exact H0.
------------ apply (@euclidean__tactics.Col__nCol__False (D) (E) (F) (H15) H14).
---------- assert (* Cut *) (euclidean__axioms.Cong A B D E) as H14.
----------- apply (@lemma__trichotomy1.lemma__trichotomy1 (A) (B) (D) (E) (H12) (H11) (H5) H13).
----------- assert (* Cut *) (euclidean__axioms.Cong B A E D) as H15.
------------ assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H15.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (E) H14).
------------- assert (* AndElim *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D)) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
exact H16.
------------ assert (* Cut *) ((euclidean__axioms.Cong A C D F) /\ ((euclidean__defs.CongA B A C E D F) /\ (euclidean__defs.CongA B C A E F D))) as H16.
------------- apply (@proposition__04.proposition__04 (B) (A) (C) (E) (D) (F) (H15) (H3) H1).
------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.Cong A B D E) /\ ((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)))).
--------------intro H17.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H18.
--------------- exact H4.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong A C D F) /\ ((euclidean__defs.CongA B A C E D F) /\ (euclidean__defs.CongA B C A E F D))) as H20.
---------------- exact H16.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H22.
----------------- exact H19.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.CongA B A C E D F) /\ (euclidean__defs.CongA B C A E F D)) as H24.
------------------ exact H21.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H26.
------------------- exact H23.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
assert (* Cut *) ((euclidean__axioms.Cong A B D E) -> (((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)) -> False)) as H32.
---------------------- intro H32.
intro H33.
apply (@H17).
-----------------------split.
------------------------ exact H32.
------------------------ exact H33.

---------------------- assert (* Cut *) (((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)) -> False) as H33.
----------------------- apply (@H32 H14).
----------------------- assert (* Cut *) ((euclidean__axioms.Cong A C D F) -> ((euclidean__defs.CongA B A C E D F) -> False)) as H34.
------------------------ intro H34.
intro H35.
apply (@H33).
-------------------------split.
-------------------------- exact H34.
-------------------------- exact H35.

------------------------ assert (* Cut *) ((euclidean__defs.CongA B A C E D F) -> False) as H35.
------------------------- apply (@H34 H20).
------------------------- assert (* Cut *) (False) as H36.
-------------------------- apply (@H35 H24).
-------------------------- assert False.
---------------------------exact H36.
--------------------------- contradiction.

Qed.
