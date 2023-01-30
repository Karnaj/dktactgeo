Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__9__5.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Require Export proposition__04.
Require Export proposition__14.
Definition lemma__angleaddition : forall A B C D E F P Q R a b c d e f p q r, (euclidean__defs.SumA A B C D E F P Q R) -> ((euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.CongA D E F d e f) -> ((euclidean__defs.SumA a b c d e f p q r) -> (euclidean__defs.CongA P Q R p q r)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro R.
intro a.
intro b.
intro c.
intro d.
intro e.
intro f.
intro p.
intro q.
intro r.
intro H.
intro H0.
intro H1.
intro H2.
assert (exists S, (euclidean__defs.CongA A B C P Q S) /\ ((euclidean__defs.CongA D E F S Q R) /\ (euclidean__axioms.BetS P S R))) as H3 by exact H.
destruct H3 as [S H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
assert (exists s, (euclidean__defs.CongA a b c p q s) /\ ((euclidean__defs.CongA d e f s q r) /\ (euclidean__axioms.BetS p s r))) as H9 by exact H2.
destruct H9 as [s H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__axioms.nCol P Q S) as H15.
- apply (@euclidean__tactics.nCol__notCol P Q S).
--apply (@euclidean__tactics.nCol__not__Col P Q S).
---apply (@lemma__equalanglesNC.lemma__equalanglesNC A B C P Q S H5).


- assert (* Cut *) (euclidean__axioms.nCol S Q R) as H16.
-- apply (@euclidean__tactics.nCol__notCol S Q R).
---apply (@euclidean__tactics.nCol__not__Col S Q R).
----apply (@lemma__equalanglesNC.lemma__equalanglesNC D E F S Q R H7).


-- assert (* Cut *) (euclidean__axioms.neq Q P) as H17.
--- assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq P S) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq S Q) /\ (euclidean__axioms.neq S P)))))) as H17.
---- apply (@lemma__NCdistinct.lemma__NCdistinct P Q S H15).
---- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H24.
--- assert (* Cut *) (euclidean__axioms.neq Q S) as H18.
---- assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H18.
----- apply (@lemma__NCdistinct.lemma__NCdistinct S Q R H16).
----- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
---- assert (* Cut *) (euclidean__axioms.neq Q R) as H19.
----- assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H19.
------ apply (@lemma__NCdistinct.lemma__NCdistinct S Q R H16).
------ destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H22.
----- assert (* Cut *) (euclidean__axioms.nCol p q s) as H20.
------ apply (@euclidean__tactics.nCol__notCol p q s).
-------apply (@euclidean__tactics.nCol__not__Col p q s).
--------apply (@lemma__equalanglesNC.lemma__equalanglesNC a b c p q s H11).


------ assert (* Cut *) (euclidean__axioms.nCol s q r) as H21.
------- apply (@euclidean__tactics.nCol__notCol s q r).
--------apply (@euclidean__tactics.nCol__not__Col s q r).
---------apply (@lemma__equalanglesNC.lemma__equalanglesNC d e f s q r H13).


------- assert (* Cut *) (euclidean__axioms.neq q p) as H22.
-------- assert (* Cut *) ((euclidean__axioms.neq p q) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq p s) /\ ((euclidean__axioms.neq q p) /\ ((euclidean__axioms.neq s q) /\ (euclidean__axioms.neq s p)))))) as H22.
--------- apply (@lemma__NCdistinct.lemma__NCdistinct p q s H20).
--------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H29.
-------- assert (* Cut *) (euclidean__axioms.neq q r) as H23.
--------- assert (* Cut *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H23.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct s q r H21).
---------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
--------- assert (* Cut *) (euclidean__axioms.neq q s) as H24.
---------- assert (* Cut *) ((euclidean__axioms.neq s q) /\ ((euclidean__axioms.neq q r) /\ ((euclidean__axioms.neq s r) /\ ((euclidean__axioms.neq q s) /\ ((euclidean__axioms.neq r q) /\ (euclidean__axioms.neq r s)))))) as H24.
----------- apply (@lemma__NCdistinct.lemma__NCdistinct s q r H21).
----------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H31.
---------- assert (* Cut *) (exists G, (euclidean__defs.Out q p G) /\ (euclidean__axioms.Cong q G Q P)) as H25.
----------- apply (@lemma__layoff.lemma__layoff q p Q P H22 H17).
----------- destruct H25 as [G H26].
destruct H26 as [H27 H28].
assert (* Cut *) (exists H29, (euclidean__defs.Out q s H29) /\ (euclidean__axioms.Cong q H29 Q S)) as H29.
------------ apply (@lemma__layoff.lemma__layoff q s Q S H24 H18).
------------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
assert (* Cut *) (exists K, (euclidean__defs.Out q r K) /\ (euclidean__axioms.Cong q K Q R)) as H34.
------------- apply (@lemma__layoff.lemma__layoff q r Q R H23 H19).
------------- destruct H34 as [K H35].
destruct H35 as [H36 H37].
assert (* Cut *) (euclidean__defs.CongA P Q S A B C) as H38.
-------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C P Q S H5).
-------------- assert (* Cut *) (euclidean__defs.CongA P Q S a b c) as H39.
--------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive P Q S A B C a b c H38 H0).
--------------- assert (* Cut *) (euclidean__defs.CongA P Q S p q s) as H40.
---------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive P Q S a b c p q s H39 H11).
---------------- assert (* Cut *) (euclidean__defs.CongA P Q S G q H30) as H41.
----------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper P Q S p q s G H30 H40 H27 H32).
----------------- assert (* Cut *) (euclidean__defs.CongA S Q R D E F) as H42.
------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D E F S Q R H7).
------------------ assert (* Cut *) (euclidean__defs.CongA S Q R d e f) as H43.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive S Q R D E F d e f H42 H1).
------------------- assert (* Cut *) (euclidean__defs.CongA S Q R s q r) as H44.
-------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive S Q R d e f s q r H43 H13).
-------------------- assert (* Cut *) (euclidean__defs.CongA S Q R H30 q K) as H45.
--------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper S Q R s q r H30 K H44 H32 H36).
--------------------- assert (* Cut *) (euclidean__axioms.nCol G q H30) as H46.
---------------------- apply (@euclidean__tactics.nCol__notCol G q H30).
-----------------------apply (@euclidean__tactics.nCol__not__Col G q H30).
------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC P Q S G q H30 H41).


---------------------- assert (* Cut *) (euclidean__defs.CongA G q H30 P Q S) as H47.
----------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric P Q S G q H30 H41).
----------------------- assert (* Cut *) ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H48.
------------------------ apply (@proposition__04.proposition__04 q G H30 Q P S H28 H33 H47).
------------------------ assert (* Cut *) (euclidean__defs.CongA H30 q K S Q R) as H49.
------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric S Q R H30 q K H45).
------------------------- assert (* Cut *) ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H50.
-------------------------- destruct H48 as [H50 H51].
destruct H51 as [H52 H53].
apply (@proposition__04.proposition__04 q H30 K Q S R H33 H37 H49).
-------------------------- assert (* Cut *) (euclidean__defs.CongA G H30 q P S Q) as H51.
--------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H48 as [H55 H56].
destruct H56 as [H57 H58].
apply (@lemma__equalanglesflip.lemma__equalanglesflip q H30 G Q S P H58).
--------------------------- assert (* Cut *) (Q = Q) as H52.
---------------------------- destruct H50 as [H52 H53].
destruct H53 as [H54 H55].
destruct H48 as [H56 H57].
destruct H57 as [H58 H59].
apply (@logic.eq__refl Point Q).
---------------------------- assert (* Cut *) (euclidean__axioms.neq S Q) as H53.
----------------------------- destruct H50 as [H53 H54].
destruct H54 as [H55 H56].
destruct H48 as [H57 H58].
destruct H58 as [H59 H60].
assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq Q R) /\ ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq Q S) /\ ((euclidean__axioms.neq R Q) /\ (euclidean__axioms.neq R S)))))) as H61.
------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct S Q R H16).
------------------------------ destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H62.
----------------------------- assert (* Cut *) (euclidean__defs.Out S Q Q) as H54.
------------------------------ destruct H50 as [H54 H55].
destruct H55 as [H56 H57].
destruct H48 as [H58 H59].
destruct H59 as [H60 H61].
apply (@lemma__ray4.lemma__ray4 S Q Q).
-------------------------------right.
left.
exact H52.

------------------------------- exact H53.
------------------------------ assert (* Cut *) (euclidean__defs.Supp P S Q Q R) as H55.
------------------------------- split.
-------------------------------- exact H54.
-------------------------------- exact H8.
------------------------------- assert (* Cut *) (euclidean__defs.RT G H30 q q H30 K) as H56.
-------------------------------- assert ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as H56 by exact H50.
assert ((euclidean__axioms.Cong H30 K S R) /\ ((euclidean__defs.CongA q H30 K Q S R) /\ (euclidean__defs.CongA q K H30 Q R S))) as __TmpHyp by exact H56.
destruct __TmpHyp as [H57 H58].
destruct H58 as [H59 H60].
assert ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as H61 by exact H48.
assert ((euclidean__axioms.Cong G H30 P S) /\ ((euclidean__defs.CongA q G H30 Q P S) /\ (euclidean__defs.CongA q H30 G Q S P))) as __TmpHyp0 by exact H61.
destruct __TmpHyp0 as [H62 H63].
destruct H63 as [H64 H65].
exists P.
exists S.
exists R.
exists Q.
exists Q.
split.
--------------------------------- exact H55.
--------------------------------- split.
---------------------------------- exact H51.
---------------------------------- exact H59.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col q s H30) as H57.
--------------------------------- destruct H50 as [H57 H58].
destruct H58 as [H59 H60].
destruct H48 as [H61 H62].
destruct H62 as [H63 H64].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear q s H30 H32).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col q H30 s) as H58.
---------------------------------- destruct H50 as [H58 H59].
destruct H59 as [H60 H61].
destruct H48 as [H62 H63].
destruct H63 as [H64 H65].
assert (* Cut *) ((euclidean__axioms.Col s q H30) /\ ((euclidean__axioms.Col s H30 q) /\ ((euclidean__axioms.Col H30 q s) /\ ((euclidean__axioms.Col q H30 s) /\ (euclidean__axioms.Col H30 s q))))) as H66.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder q s H30 H57).
----------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col q p G) as H59.
----------------------------------- destruct H50 as [H59 H60].
destruct H60 as [H61 H62].
destruct H48 as [H63 H64].
destruct H64 as [H65 H66].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear q p G H27).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col G q p) as H60.
------------------------------------ destruct H50 as [H60 H61].
destruct H61 as [H62 H63].
destruct H48 as [H64 H65].
destruct H65 as [H66 H67].
assert (* Cut *) ((euclidean__axioms.Col p q G) /\ ((euclidean__axioms.Col p G q) /\ ((euclidean__axioms.Col G q p) /\ ((euclidean__axioms.Col q G p) /\ (euclidean__axioms.Col G p q))))) as H68.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder q p G H59).
------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H73.
------------------------------------ assert (* Cut *) (q = q) as H61.
------------------------------------- destruct H50 as [H61 H62].
destruct H62 as [H63 H64].
destruct H48 as [H65 H66].
destruct H66 as [H67 H68].
apply (@logic.eq__refl Point q).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col G q q) as H62.
-------------------------------------- right.
right.
left.
exact H61.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq q p) as H63.
--------------------------------------- destruct H50 as [H63 H64].
destruct H64 as [H65 H66].
destruct H48 as [H67 H68].
destruct H68 as [H69 H70].
exact H22.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq p q) as H64.
---------------------------------------- destruct H50 as [H64 H65].
destruct H65 as [H66 H67].
destruct H48 as [H68 H69].
destruct H69 as [H70 H71].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric q p H63).
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol p q H30) as H65.
----------------------------------------- destruct H50 as [H65 H66].
destruct H66 as [H67 H68].
destruct H48 as [H69 H70].
destruct H70 as [H71 H72].
apply (@euclidean__tactics.nCol__notCol p q H30).
------------------------------------------apply (@euclidean__tactics.nCol__not__Col p q H30).
-------------------------------------------apply (@lemma__NChelper.lemma__NChelper G q H30 p q H46 H60 H62 H64).


----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q H30 p) as H66.
------------------------------------------ destruct H50 as [H66 H67].
destruct H67 as [H68 H69].
destruct H48 as [H70 H71].
destruct H71 as [H72 H73].
assert (* Cut *) ((euclidean__axioms.nCol q p H30) /\ ((euclidean__axioms.nCol q H30 p) /\ ((euclidean__axioms.nCol H30 p q) /\ ((euclidean__axioms.nCol p H30 q) /\ (euclidean__axioms.nCol H30 q p))))) as H74.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder p q H30 H65).
------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H77.
------------------------------------------ assert (* Cut *) (euclidean__axioms.TS p q H30 r) as H67.
------------------------------------------- exists s.
split.
-------------------------------------------- exact H14.
-------------------------------------------- split.
--------------------------------------------- exact H58.
--------------------------------------------- exact H66.
------------------------------------------- assert (* Cut *) (euclidean__axioms.TS r q H30 p) as H68.
-------------------------------------------- destruct H50 as [H68 H69].
destruct H69 as [H70 H71].
destruct H48 as [H72 H73].
destruct H73 as [H74 H75].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric q H30 p r H67).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q H30 q) as H69.
--------------------------------------------- right.
left.
exact H61.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Out q K r) as H70.
---------------------------------------------- destruct H50 as [H70 H71].
destruct H71 as [H72 H73].
destruct H48 as [H74 H75].
destruct H75 as [H76 H77].
apply (@lemma__ray5.lemma__ray5 q r K H36).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.TS K q H30 p) as H71.
----------------------------------------------- destruct H50 as [H71 H72].
destruct H72 as [H73 H74].
destruct H48 as [H75 H76].
destruct H76 as [H77 H78].
apply (@lemma__9__5.lemma__9__5 q H30 p r K q H68 H70 H69).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.TS p q H30 K) as H72.
------------------------------------------------ destruct H50 as [H72 H73].
destruct H73 as [H74 H75].
destruct H48 as [H76 H77].
destruct H77 as [H78 H79].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric q H30 K p H71).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out q G p) as H73.
------------------------------------------------- destruct H50 as [H73 H74].
destruct H74 as [H75 H76].
destruct H48 as [H77 H78].
destruct H78 as [H79 H80].
apply (@lemma__ray5.lemma__ray5 q p G H27).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G q H30 K) as H74.
-------------------------------------------------- destruct H50 as [H74 H75].
destruct H75 as [H76 H77].
destruct H48 as [H78 H79].
destruct H79 as [H80 H81].
apply (@lemma__9__5.lemma__9__5 q H30 K p G q H72 H73 H69).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS K q H30 G) as H75.
--------------------------------------------------- destruct H50 as [H75 H76].
destruct H76 as [H77 H78].
destruct H48 as [H79 H80].
destruct H80 as [H81 H82].
apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric q H30 G K H74).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q H30) as H76.
---------------------------------------------------- destruct H50 as [H76 H77].
destruct H77 as [H78 H79].
destruct H48 as [H80 H81].
destruct H81 as [H82 H83].
apply (@lemma__raystrict.lemma__raystrict q s H30 H32).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H30 q) as H77.
----------------------------------------------------- destruct H50 as [H77 H78].
destruct H78 as [H79 H80].
destruct H48 as [H81 H82].
destruct H82 as [H83 H84].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric q H30 H76).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H30 q q) as H78.
------------------------------------------------------ destruct H50 as [H78 H79].
destruct H79 as [H80 H81].
destruct H48 as [H82 H83].
destruct H83 as [H84 H85].
apply (@lemma__ray4.lemma__ray4 H30 q q).
-------------------------------------------------------right.
left.
exact H61.

------------------------------------------------------- exact H77.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS G H30 K) as H79.
------------------------------------------------------- destruct H50 as [H79 H80].
destruct H80 as [H81 H82].
destruct H48 as [H83 H84].
destruct H84 as [H85 H86].
assert (* Cut *) (forall A0 B0 C0 D0 E0, (euclidean__defs.RT A0 B0 C0 D0 B0 E0) -> ((euclidean__defs.Out B0 C0 D0) -> ((euclidean__axioms.TS E0 D0 B0 A0) -> (euclidean__axioms.BetS A0 B0 E0)))) as H87.
-------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Supp A0 B0 C0 D0 E0) /\ (euclidean__axioms.BetS A0 B0 E0)) as __2.
--------------------------------------------------------- apply (@proposition__14.proposition__14 A0 B0 C0 D0 E0 __ __0 __1).
--------------------------------------------------------- destruct __2 as [__2 __3].
exact __3.
-------------------------------------------------------- apply (@H87 G H30 q q K H56 H78 H75).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G K P R) as H80.
-------------------------------------------------------- destruct H50 as [H80 H81].
destruct H81 as [H82 H83].
destruct H48 as [H84 H85].
destruct H85 as [H86 H87].
apply (@euclidean__axioms.cn__sumofparts G H30 K P S R H84 H80 H79 H8).
-------------------------------------------------------- assert (* Cut *) (P = P) as H81.
--------------------------------------------------------- destruct H50 as [H81 H82].
destruct H82 as [H83 H84].
destruct H48 as [H85 H86].
destruct H86 as [H87 H88].
apply (@logic.eq__refl Point P).
--------------------------------------------------------- assert (* Cut *) (R = R) as H82.
---------------------------------------------------------- destruct H50 as [H82 H83].
destruct H83 as [H84 H85].
destruct H48 as [H86 H87].
destruct H87 as [H88 H89].
apply (@logic.eq__refl Point R).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q P P) as H83.
----------------------------------------------------------- destruct H50 as [H83 H84].
destruct H84 as [H85 H86].
destruct H48 as [H87 H88].
destruct H88 as [H89 H90].
apply (@lemma__ray4.lemma__ray4 Q P P).
------------------------------------------------------------right.
left.
exact H81.

------------------------------------------------------------ exact H17.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out Q R R) as H84.
------------------------------------------------------------ destruct H50 as [H84 H85].
destruct H85 as [H86 H87].
destruct H48 as [H88 H89].
destruct H89 as [H90 H91].
apply (@lemma__ray4.lemma__ray4 Q R R).
-------------------------------------------------------------right.
left.
exact H82.

------------------------------------------------------------- exact H19.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol P S Q) as H85.
------------------------------------------------------------- destruct H50 as [H85 H86].
destruct H86 as [H87 H88].
destruct H48 as [H89 H90].
destruct H90 as [H91 H92].
assert (* Cut *) ((euclidean__axioms.nCol Q P S) /\ ((euclidean__axioms.nCol Q S P) /\ ((euclidean__axioms.nCol S P Q) /\ ((euclidean__axioms.nCol P S Q) /\ (euclidean__axioms.nCol S Q P))))) as H93.
-------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder P Q S H15).
-------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H100.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P S R) as H86.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H8.
-------------------------------------------------------------- assert (* Cut *) (P = P) as H87.
--------------------------------------------------------------- destruct H50 as [H87 H88].
destruct H88 as [H89 H90].
destruct H48 as [H91 H92].
destruct H92 as [H93 H94].
exact H81.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P S P) as H88.
---------------------------------------------------------------- right.
left.
exact H87.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P R) as H89.
----------------------------------------------------------------- destruct H50 as [H89 H90].
destruct H90 as [H91 H92].
destruct H48 as [H93 H94].
destruct H94 as [H95 H96].
assert (* Cut *) ((euclidean__axioms.neq S R) /\ ((euclidean__axioms.neq P S) /\ (euclidean__axioms.neq P R))) as H97.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal P S R H8).
------------------------------------------------------------------ destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H101.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P R Q) as H90.
------------------------------------------------------------------ destruct H50 as [H90 H91].
destruct H91 as [H92 H93].
destruct H48 as [H94 H95].
destruct H95 as [H96 H97].
apply (@euclidean__tactics.nCol__notCol P R Q).
-------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col P R Q).
--------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper P S Q P R H85 H88 H86 H89).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol P Q R) as H91.
------------------------------------------------------------------- destruct H50 as [H91 H92].
destruct H92 as [H93 H94].
destruct H48 as [H95 H96].
destruct H96 as [H97 H98].
assert (* Cut *) ((euclidean__axioms.nCol R P Q) /\ ((euclidean__axioms.nCol R Q P) /\ ((euclidean__axioms.nCol Q P R) /\ ((euclidean__axioms.nCol P Q R) /\ (euclidean__axioms.nCol Q R P))))) as H99.
-------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder P R Q H90).
-------------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H106.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q P q G) as H92.
-------------------------------------------------------------------- destruct H50 as [H92 H93].
destruct H93 as [H94 H95].
destruct H48 as [H96 H97].
destruct H97 as [H98 H99].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric Q q G P H28).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong Q R q K) as H93.
--------------------------------------------------------------------- destruct H50 as [H93 H94].
destruct H94 as [H95 H96].
destruct H48 as [H97 H98].
destruct H98 as [H99 H100].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric Q q K R H37).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong P R G K) as H94.
---------------------------------------------------------------------- destruct H50 as [H94 H95].
destruct H95 as [H96 H97].
destruct H48 as [H98 H99].
destruct H99 as [H100 H101].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric P G K R H80).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA P Q R p q r) as H95.
----------------------------------------------------------------------- exists P.
exists R.
exists G.
exists K.
split.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H27.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H36.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------ exact H91.
----------------------------------------------------------------------- exact H95.
Qed.
